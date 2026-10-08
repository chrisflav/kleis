import Kleis.Token.Issue

/-!
# Revocation

A biscuit carries one revocation identifier per block, and every identifier of
every block is checked.  So revoking a token also revokes every attenuation
anybody has ever derived from it — which is the behaviour a lost laptop calls
for, and the reason the list is keyed on identifiers rather than on tokens.

The list is a file of hex identifiers, one per line, read fresh whenever the
daemon is asked to reload.  Small enough to keep in memory, append-only in
practice, and readable by a person deciding whether a revocation took.
-/

namespace Kleis
namespace Token

open LeanBiscuit

/-- The revocation list, in memory. -/
structure Revocations where
  /-- The revoked identifiers, hex. -/
  ids : List String
  deriving Inhabited

/-- Read the revocation list. -/
def loadRevocations : IO Revocations := do
  match ← Store.read? (← Dirs.revocations) with
  | none => return { ids := [] }
  | some text =>
    let ids := ((text.splitOn "\n").map Str.trim).filter fun l =>
      !l.isEmpty && !l.startsWith "#"
    return { ids }

/-- Revoke every identifier of a token, by its recorded identifiers. -/
def revoke (ids : List String) : IO Unit := do
  let path ← Dirs.revocations
  let existing ← loadRevocations
  for id in ids do
    if !existing.ids.contains id then
      Store.appendLine path id

/-- Record that a token was issued, so it can be listed and revoked later. -/
def recordIssued (r : IssuedRecord) : IO Unit := do
  let dir ← Dirs.issued
  let name := (r.revocationIds.headD "unknown")
  Store.writeSecret (dir / s!"{name}.json") (Bytes.ofString (Json.render r.toJson))

/-- Every token that was issued and has not been forgotten. -/
def listIssued : IO (Array IssuedRecord) := do
  let files ← Store.listFiles (← Dirs.issued) "json"
  let mut out : Array IssuedRecord := #[]
  for f in files do
    if let some text ← Store.read? f then
      if let .ok j := Json.parse text then
        if let .ok r := IssuedRecord.ofJson j then
          out := out.push r
  return out

/-- Find an issued record by one of its revocation identifiers, exactly.

The record is filed under its first identifier, which is the one an issuer is
handed back first, so that one is a single file read rather than a scan of
every token ever issued; any other identifier falls back to the scan. -/
def findIssuedExactly? (id : String) : IO (Option IssuedRecord) := do
  if !id.isEmpty && id.all Char.isHexDigit then
    if let some text ← Store.read? ((← Dirs.issued) / s!"{id}.json") then
      if let .ok j := Json.parse text then
        if let .ok r := IssuedRecord.ofJson j then
          if r.revocationIds.contains id then return some r
  return (← listIssued).find? (·.revocationIds.contains id)

/-- Find an issued record by any of its revocation identifiers, or by a prefix
of one — so that a person can revoke by the short form the CLI prints. -/
def findIssued? (records : Array IssuedRecord) (needle : String) :
    Option IssuedRecord :=
  Array.find? (fun r => r.revocationIds.any fun id => id.startsWith needle) records

end Token
end Kleis
