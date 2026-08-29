import Auth.Ca.X509
import Auth.Store
import Auth.Net.Tls

/-!
# The local certificate authority

Interception needs a certificate for whatever host the client asked for, and it
needs it during the handshake, so certificates are minted on demand and cached
for the life of the process.

The root lives in the data directory: a private key that never leaves the host,
and a certificate the owner installs where their tools look — and only there.
`auth setup` writes it into git's and curl's trust configuration, never into
the system store, because a CA in the system store is trusted by everything on
the machine and this one only needs to be trusted by the tools being proxied.
-/

namespace Auth
namespace Ca

open LeanBiscuit
open LeanBiscuit (Bytes)

/-- A key and the certificate that goes with it. -/
structure Pair where
  /-- The private key, PEM. -/
  keyPem : String
  /-- The certificate chain, PEM, leaf first. -/
  certPem : String
  deriving Inhabited

/-- The root: its secret scalar and its certificate. -/
structure Root where
  /-- The 32 byte secret scalar. -/
  secret : Bytes
  /-- The self-signed certificate, DER. -/
  der : Bytes
  /-- The issuer `Name`, reused verbatim in every leaf so that the chain links
  by exact byte equality rather than by a re-encoding that might differ. -/
  issuerName : Bytes

/-- How long a freshly minted root is good for. -/
def rootLifetime : Nat := 10 * 365 * 86400

/-- How long a leaf is good for.  Short, because they are minted on demand and
never travel: the only thing a long-lived leaf would buy is a longer window for
one that leaked. -/
def leafLifetime : Nat := 30 * 86400

/-- Backdate the start of validity, so a client whose clock is a few minutes
behind does not reject a certificate minted a moment ago. -/
def clockSkew : Nat := 3600

/-- A random secp256r1 scalar in `[1, n)`. -/
def randomScalar : IO Bytes := do
  let rec go (attempts : Nat) : IO Bytes := do
    match attempts with
    | 0 => throw (IO.userError "could not generate a key")
    | n + 1 =>
      let b ← Store.randomBytes 32
      let d := Bytes.toNatBE b
      if d == 0 || d ≥ P256.n then go n else pure b
  go 16

/-- A random certificate serial: 16 bytes, top bit cleared so the DER integer
is positive. -/
def randomSerial : IO Nat := do
  let b ← Store.randomBytes 16
  return (Bytes.toNatBE b) % (2 ^ 127)

/-- Create a root, or load the one that is already there. -/
def loadOrCreateRoot : IO Root := do
  let dir ← Dirs.ca
  let keyPath := dir / "ca.key"
  let certPath := dir / "ca.der"
  match ← Store.readBin? keyPath, ← Store.readBin? certPath with
  | some secret, some der =>
    let commonName := "auth local CA"
    return { secret, der, issuerName := X509.name commonName (some "auth") }
  | _, _ => do
    let secret ← randomScalar
    let some point := X509.uncompressedPoint secret
      | throw (IO.userError "the generated key is not on the curve")
    let now ← Store.now
    let serial ← randomSerial
    let commonName := "auth local CA"
    let spec : X509.Spec := {
      serial, commonName, organization := some "auth"
      notBefore := now - clockSkew, notAfter := now + rootLifetime, isCa := true }
    let der ← match X509.certificate spec point secret none with
      | .ok d => pure d
      | .error e => throw (IO.userError e)
    Store.writeSecret keyPath secret
    Store.writeSecret certPath der
    Store.writePublic (dir / "ca.crt") (X509.certificatePem der)
    return { secret, der, issuerName := X509.name commonName (some "auth") }

/-- The root certificate as PEM, which is what a client is told to trust. -/
def Root.pem (r : Root) : String := X509.certificatePem r.der

/-- Mint a leaf for a host.

The host goes in the subject alternative name, which is the only field a
verifier looks at.  A wildcard is issued alongside the exact name when the host
has a parent, so that one certificate covers `api.github.com` and
`codeload.github.com` if a connection is reused across them. -/
def Root.mint (r : Root) (host : String) : IO Pair := do
  let secret ← randomScalar
  let some point := X509.uncompressedPoint secret
    | throw (IO.userError "the generated key is not on the curve")
  let now ← Store.now
  let serial ← randomSerial
  let spec : X509.Spec := {
    serial, commonName := host, organization := some "auth"
    altNames := [host]
    notBefore := now - clockSkew, notAfter := now + leafLifetime, isCa := false }
  let der ← match X509.certificate spec point r.secret (some r.issuerName) with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let keyPem ← match X509.privateKeyPem secret with
    | .ok p => pure p
    | .error e => throw (IO.userError e)
  -- The chain is leaf then root, so a client that trusts the root can build a
  -- path without having to have the intermediate to hand.
  return { keyPem, certPem := X509.certificatePem der ++ r.pem }

/-- A cache of TLS server contexts, one per host.

Minting is a scalar multiplication and a signature — not free, and a client
opening ten connections to one host should pay for it once.  Contexts rather
than certificates are cached because building the context is what OpenSSL
charges for. -/
structure Cache where
  /-- The root doing the signing. -/
  root : Root
  /-- Host to context. -/
  entries : IO.Ref (Array (String × Net.Tls.Context))

/-- A fresh cache. -/
def Cache.create (root : Root) : IO Cache := do
  return { root, entries := ← IO.mkRef #[] }

/-- The server context for a host, minting and caching if needed. -/
def Cache.contextFor (c : Cache) (host : String) : IO Net.Tls.Context := do
  let host := Str.toLowerAscii host
  let current ← c.entries.get
  match Array.find? (fun (h, _) => h == host) current with
  | some (_, ctx) => return ctx
  | none => do
    let pair ← c.root.mint host
    let ctx ← Net.Tls.mkServerContext pair.certPem pair.keyPem
    c.entries.modify (·.push (host, ctx))
    return ctx

end Ca
end Auth
