import Auth.Policy.Authorize
import Auth.Util.Base64

/-!
# Secrets, and the one place they are spent

A `Secret` has no `ToString`, no `Repr`, no `ToJson` and a private field.  The
only way to get the bytes out is `bind`, which is in this module because
`private` in Lean is per-module: putting the elimination anywhere else would
mean exposing the field, and then the guarantee would be a convention rather
than a compiler error.

`bind` takes an `Auth.Policy.AuthorizedRequest`, whose constructor is private
to the authorizer.  So the type of this function says: a credential is attached
to a request only after a decision, and only to a host the manifest bound it
to.  Neither is a rule somebody has to remember.

What can safely be observed about a secret is its length and a fingerprint —
the first bytes of its SHA-256 — which is what the audit log records so that
"which credential was this" has an answer that is not the credential.
-/

namespace Auth
namespace Credential

open LeanBiscuit
open Policy (AuthorizedRequest)

/-- An upstream credential.  Opaque by construction. -/
structure Secret where
  private mk ::
  private raw : ByteArray

/-- Wrap bytes as a secret. -/
def Secret.ofBytes (b : ByteArray) : Secret := ⟨b⟩

/-- Wrap text as a secret. -/
def Secret.ofString (s : String) : Secret := ⟨s.toUTF8⟩

/-- How long it is.  Safe to log: a length is not a secret, and a length of
zero is a misconfiguration worth seeing. -/
def Secret.size (s : Secret) : Nat := s.raw.size

/-- A stable identifier for a secret that is not the secret: the first eight
bytes of its SHA-256, hex encoded.  Two log lines naming the same fingerprint
spent the same credential; nobody reading the log learns what it was. -/
def Secret.fingerprint (s : Secret) : String :=
  Bytes.toHex (Bytes.take (Sha256.hash s.raw) 8)

/-- The raw bytes, for the store to encrypt.

This is the second elimination, and it exists only so that a secret can be
written to disk under a key.  It is not `private` because the store is a
separate module, so the guarantee here is weaker than for `bind`: what the type
system enforces is that the bytes cannot be obtained *by accident*, and a
reviewer looking for every place a credential is read has two call sites to
check rather than a codebase to search. -/
def Secret.reveal (s : Secret) : ByteArray := s.raw

/-- Render an injection template.

`{{secret}}` is the secret as text and `{{secret_base64}}` is it base64
encoded.  Nothing else is substituted: a template is not a general expression
language, because a template that could compute would be a second place where
policy lives. -/
private def render (template : String) (s : Secret) : String :=
  let text := match String.fromUTF8? s.raw with
    | some t => t
    | none => Base64.encode s.raw
  let step (acc : String) (needle replacement : String) : String :=
    replacement.intercalate (acc.splitOn needle)
  step (step template "{{secret_base64}}" (Base64.encode s.raw)) "{{secret}}" text

/-- Why a credential could not be attached. -/
inductive BindError where
  /-- The credential is not bound to the request's host. -/
  | hostNotBound (host : String)
  /-- The manifest declares no injection that applies to this host. -/
  | noInjection
  deriving Repr

/-- Describe a binding failure. -/
def BindError.toString : BindError → String
  | .hostNotBound h => s!"the credential is not bound to `{h}`"
  | .noInjection => "the manifest declares no injection for this credential on this host"

/-- Attach a credential to an authorized request.

The host check is repeated here even though the manifest was already consulted
when the request was routed, because this function is also what a redirect goes
through: a `302` to a host outside the binding is followed, if at all, without
the credential.  Checking at the point of use rather than at the point of
routing is what makes that safe. -/
def bind (r : AuthorizedRequest) (s : Secret) : Except BindError Model.Request := do
  let m := r.manifest
  let req := r.request
  if !m.mayCredentialReach req.host then throw (.hostNotBound req.host)
  let applicable := m.credential.inject.filter (·.appliesTo req.host)
  if applicable.isEmpty then throw .noInjection
  let headers := Http.Headers.removeAll req.headers
    (m.credential.strip ++ ["authorization", "proxy-authorization"])
  let mut out := { req with headers }
  for inj in applicable do
    let value := render inj.template s
    match inj.kind with
    | .header => out := { out with headers := Http.Headers.set out.headers inj.name value }
    | .basic =>
      out := { out with headers :=
        Http.Headers.set out.headers inj.name s!"Basic {Base64.encode value.toUTF8}" }
    | .query =>
      let kept := Array.filter (fun (k, _) => k != inj.name) out.query
      out := { out with query := kept.push (inj.name, value) }
  pure out

/-- Strip what must never reach the origin, for a request that is being
forwarded *without* a credential — a host the manifest claims but the
credential is not bound to. -/
def stripOnly (r : AuthorizedRequest) : Model.Request :=
  let names := r.manifest.credential.strip ++ ["authorization", "proxy-authorization"]
  { r.request with headers := Http.Headers.removeAll r.request.headers names }

end Credential
end Auth
