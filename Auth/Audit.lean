import Auth.Policy.Authorize
import Auth.Store

/-!
# The audit log

One record per decision, appended, hash chained.

Chained because the interesting attack on an audit log is deletion, not
forgery: an attacker who spent a credential wants the line about it gone.  Each
record carries the SHA-256 of the previous line, so removing one breaks the
chain at that point and `auth audit verify` says where.

Because authorization is a pure function of the facts, and the facts are in the
record along with the manifest and grant versions, a record replays to the same
decision.  "Why was this allowed" is a question with an answer, months later,
offline.

Secrets never enter the log.  A record names the credential and its
fingerprint, never its value.
-/

namespace Auth

open LeanBiscuit

/-- One decision, as it is written down. -/
structure AuditRecord where
  /-- When. -/
  time : Nat
  /-- The request identifier, which also appears in the proxy's error
  responses so a bearer can quote it. -/
  requestId : String
  /-- What was asked for. -/
  method : String
  /-- The absolute URL. -/
  url : String
  /-- The client's address. -/
  clientIp : String
  /-- The service manifest's name and version. -/
  service : String
  /-- The manifest's SHA-256. -/
  manifestVersion : String
  /-- The grant's name. -/
  grant : String
  /-- The grant's SHA-256. -/
  grantVersion : String
  /-- The token's revocation identifiers. -/
  revocationIds : List String
  /-- Whether it was allowed. -/
  allowed : Bool
  /-- The matched policy index, or the reason for refusal. -/
  outcome : String
  /-- Every fact the authorizer saw, as datalog. -/
  facts : List String
  /-- Which credential was spent, and its fingerprint — never its value. -/
  credential : Option (String × String)
  /-- The upstream status, once there is one. -/
  status : Option Nat
  deriving Inhabited

/-- Render a record, without the chain link. -/
def AuditRecord.toJson (r : AuditRecord) : Json :=
  .obj [
    ("time", .num (toString r.time)),
    ("request_id", .str r.requestId),
    ("method", .str r.method),
    ("url", .str r.url),
    ("client_ip", .str r.clientIp),
    ("service", .str r.service),
    ("manifest_version", .str r.manifestVersion),
    ("grant", .str r.grant),
    ("grant_version", .str r.grantVersion),
    ("revocation_ids", .arr (r.revocationIds.map Json.str)),
    ("allowed", .bool r.allowed),
    ("outcome", .str r.outcome),
    ("facts", .arr (r.facts.map Json.str)),
    ("credential", match r.credential with
      | some (name, fp) => .obj [("name", .str name), ("fingerprint", .str fp)]
      | none => .null),
    ("status", match r.status with | some s => .num (toString s) | none => .null)]

/-- The genesis link, for the first record in a log. -/
def auditGenesis : String := String.ofList (List.replicate 64 '0')

/-- The link a record contributes to the chain: the hash of the previous link
and this record's body. -/
def auditLink (previous : String) (body : String) : String :=
  Bytes.toHex (Sha256.hash (Bytes.ofString (previous ++ "\n" ++ body)))

/-- The last link in the log, or the genesis value for an empty one. -/
def auditTip : IO String := do
  match ← Store.read? (← Dirs.auditLog) with
  | none => return auditGenesis
  | some text =>
    let lines := (text.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
    match lines.getLast? with
    | none => return auditGenesis
    | some last =>
      match Json.parse last with
      | .ok j => return (j.str? "link").getD auditGenesis
      | .error _ => return auditGenesis

/-- Append a record, linking it to the tip. -/
def auditAppend (r : AuditRecord) : IO Unit := do
  let previous ← auditTip
  let body := Json.render r.toJson
  let link := auditLink previous body
  let line := Json.render (.obj [("previous", .str previous), ("link", .str link),
                                 ("record", ← match Json.parse body with
                                   | .ok j => pure j
                                   | .error _ => pure (.str body))])
  Store.appendLine (← Dirs.auditLog) line

/-- Check the chain, returning the number of records and the first line whose
link does not follow. -/
def auditVerify : IO (Nat × Option Nat) := do
  match ← Store.read? (← Dirs.auditLog) with
  | none => return (0, none)
  | some text =>
    let lines := (text.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
    let mut expected := auditGenesis
    let mut index := 0
    for line in lines do
      match Json.parse line with
      | .error _ => return (index, some index)
      | .ok j =>
        let previous := (j.str? "previous").getD ""
        let link := (j.str? "link").getD ""
        let body := match j.field? "record" with
          | some b => Json.render b
          | none => ""
        if previous != expected then return (index, some index)
        if auditLink previous body != link then return (index, some index)
        expected := link
        index := index + 1
    return (index, none)

end Auth
