import Kleis.Credential.Secret
import Kleis.Crypto.Aead
import Kleis.Store

/-!
# The credential store

Credentials live encrypted under a master key, one file each.  What is *not*
encrypted is the record around them — the name, the service, the provider and
its settings — because the daemon has to list and route on those without
unlocking anything, and none of them is a secret.

The record is bound into the ciphertext as associated data.  Moving a
credential's encrypted material into another record, so that a permissive
grant's name points at a powerful token, changes the associated data and the
tag stops verifying.  Encryption alone would not have caught that.

## The master key

In order: `$KLEIS_STORE_KEY` (hex, for a machine), `$KLEIS_STORE_PASSPHRASE`
(stretched with PBKDF2 against a stored salt), or a key file generated on first
use.  The key file is the default because it is the one that works without the
owner being present, which a daemon restarting at three in the morning needs.
-/

namespace Kleis
namespace Credential

open LeanBiscuit

/-- A stored credential, as it sits on disk. -/
structure Record where
  /-- The name a grant refers to, such as `github/chrisflav`. -/
  name : String
  /-- The service whose manifest governs it. -/
  service : String
  /-- Which provider turns the material into a live secret. -/
  provider : String
  /-- Provider settings.  Never secret: a client id and a token endpoint are
  configuration, and keeping them readable is what lets the daemon report on a
  credential it cannot currently decrypt. -/
  config : Json
  /-- When it was installed. -/
  created : Nat
  /-- The AEAD nonce, hex. -/
  nonce : String
  /-- The encrypted material, hex. -/
  ciphertext : String
  deriving Inhabited

/-- Render a record as JSON. -/
def Record.toJson (r : Record) : Json :=
  .obj [("name", .str r.name), ("service", .str r.service), ("provider", .str r.provider),
        ("config", r.config), ("created", .num (toString r.created)),
        ("nonce", .str r.nonce), ("ciphertext", .str r.ciphertext)]

/-- Read a record from JSON. -/
def Record.ofJson (j : Json) : Except String Record := do
  let get (k : String) : Except String String := match j.str? k with
    | some v => .ok v
    | none => throw s!"a credential record needs `{k}`"
  pure { name := ← get "name", service := ← get "service", provider := ← get "provider"
         config := (j.field? "config").getD (.obj [])
         created := ((j.int? "created").getD 0).toNat
         nonce := ← get "nonce", ciphertext := ← get "ciphertext" }

/-- What a record's ciphertext is bound to.  Changing any of it invalidates the
tag, so material cannot be moved between records. -/
private def aadOf (r : Record) : Bytes :=
  Bytes.ofString s!"kleis/credential/v1\n{r.name}\n{r.service}\n{r.provider}"

/-- Resolve the master key, generating a key file if that is the route and
there is nothing there yet. -/
def masterKey : IO Bytes := do
  if let some hex ← IO.getEnv "KLEIS_STORE_KEY" then
    match Bytes.ofHex? (hex.trimAscii.toString) with
    | some k => if k.size == 32 then return k
                else throw (IO.userError "KLEIS_STORE_KEY must be 32 bytes of hex")
    | none => throw (IO.userError "KLEIS_STORE_KEY is not hexadecimal")
  let dataDir ← Dirs.data
  if let some pass ← IO.getEnv "KLEIS_STORE_PASSPHRASE" then
    let saltPath := dataDir / "store.salt"
    let salt ← match ← Store.readBin? saltPath with
      | some s => pure s
      | none => do
        let s ← Store.randomBytes 16
        Store.writeSecret saltPath s
        pure s
    return Aead.pbkdf2 (Bytes.ofString pass) salt Aead.defaultIterations 32
  let keyPath := dataDir / "store.key"
  match ← Store.readBin? keyPath with
  | some k => if k.size == 32 then return k
              else throw (IO.userError s!"{keyPath} is not a 32 byte key")
  | none => do
    let k ← Store.randomBytes 32
    Store.writeSecret keyPath k
    return k

/-- The file a credential lives in.  The name is hashed rather than used as a
path, so that a name containing a slash — which every sensible naming scheme
has — cannot escape the directory. -/
def pathOf (name : String) : IO System.FilePath := do
  let digest := Bytes.toHex (Bytes.take (Sha256.hash (Bytes.ofString name)) 16)
  return (← Dirs.credentials) / s!"{digest}.json"

/-- Install a credential, replacing any of the same name. -/
def save (name service provider : String) (config : Json) (material : Secret) : IO Unit := do
  let key ← masterKey
  let nonce ← Store.randomBytes 12
  let skeleton : Record :=
    { name, service, provider, config, created := ← Store.now
      nonce := Bytes.toHex nonce, ciphertext := "" }
  let sealed := Aead.encrypt key nonce (aadOf skeleton) (Secret.reveal material)
  let record := { skeleton with ciphertext := Bytes.toHex sealed }
  Store.writeSecret (← pathOf name) (Bytes.ofString (Json.render record.toJson))

/-- Read a record without decrypting it. -/
def load? (name : String) : IO (Option Record) := do
  match ← Store.read? (← pathOf name) with
  | none => return none
  | some text =>
    match Json.parse text >>= fun j => Record.ofJson j with
    | .ok r => return some r
    | .error e => throw (IO.userError s!"the credential `{name}` is corrupt: {e}")

/-- Every installed credential. -/
def list : IO (Array Record) := do
  let files ← Store.listFiles (← Dirs.credentials) "json"
  let mut out : Array Record := #[]
  for f in files do
    if let some text ← Store.read? f then
      if let .ok r := Json.parse text >>= fun j => Record.ofJson j then
        out := out.push r
  return out

/-- Decrypt a record's material.

A failure here is reported as a bad master key rather than a bad file: those
are the same event from the daemon's point of view, and guessing which it was
would be telling an attacker whether a key was close. -/
def unlock (r : Record) : IO Secret := do
  let key ← masterKey
  let some nonce := Bytes.ofHex? r.nonce
    | throw (IO.userError s!"the credential `{r.name}` has a malformed nonce")
  let some sealed := Bytes.ofHex? r.ciphertext
    | throw (IO.userError s!"the credential `{r.name}` has malformed ciphertext")
  match Aead.decrypt? key nonce (aadOf r) sealed with
  | some plain => return Secret.ofBytes plain
  | none => throw (IO.userError
      s!"the credential `{r.name}` could not be decrypted: wrong master key, or the file was altered")

/-- Remove a credential. -/
def remove (name : String) : IO Bool := do
  let p ← pathOf name
  if ← p.pathExists then
    IO.FS.removeFile p
    return true
  else return false

end Credential
end Kleis
