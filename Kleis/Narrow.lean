import Kleis.Service.Registry
import Kleis.Spec

/-!
# Narrowings

A narrowing takes away from a token, per service, in the words of the service's extension:

```
mail: only read, flag
caldav: only read
services: mail, caldav
```

The last form confines the token to the services it names: a request to any other service is
refused (`reject if request_service($s), !["mail", "caldav"].contains($s);`). Passthrough hosts
belong to no service and are not affected.

It is compiled into `reject if` checks, one per service:

```
reject if request_service("mail"), operation($op), !["list_mailboxes", …, "set_flags"].contains($op);
```

A reject and not a `check if`: a token's checks are also evaluated where there is no request at
all — at the daemon's own endpoints, for a passthrough tunnel (`Proxy.tokenHolds`) — and a
`check if request_service(…)` would fail there, locking a narrowed token out of its own card. A
reject fires only on a request to the service it names, and leaves everything else alone.

A narrowing only adds checks, so it can only refuse. Groups are expanded when it is compiled; a
spec edited afterwards does not change it.
-/

namespace Kleis
namespace Narrow

open LeanBiscuit

/-- Compile one narrowing line to the datalog of its reject. -/
def toDatalog (registry : Service.Registry) (line : String) : Except String String := do
  let some (svc, rest) := Str.splitOnce? line ":"
    | throw s!"a narrowing is `service: only op, op`, not `{line}`"
  let svc := Str.trim svc
  let rest := Str.trim rest
  -- `services: zulip, mail` confines the token to those services: a request to any other is
  -- refused, whatever its spec or grants reach. Passthrough is not a service and is unaffected.
  if svc == "services" then
    let names := (rest.splitOn ",").map Str.trim |>.filter (!·.isEmpty)
    if names.isEmpty then throw "`services:` names at least one service"
    for n in names do
      if (registry.manifest? n).isNone then throw s!"`{n}` is not a service kleis knows"
    let list := Spec.Value.render (.list (names.eraseDups.map .str))
    return s!"reject if request_service($s), !{list}.contains($s);"
  if !rest.startsWith "only " then throw s!"a narrowing says `only`: `{svc}: only read`"
  let names := ((Str.stripPrefix rest "only ").splitOn ",").map Str.trim |>.filter (!·.isEmpty)
  if names.isEmpty then throw s!"the narrowing of `{svc}` names no operation"
  let some manifest := registry.manifest? svc
    | throw s!"`{svc}` is not a service kleis knows"
  let ops := Service.Manifest.operations manifest
  let mut allowed : List String := []
  for n in names do
    let expanded := match registry.extension? svc with
      | some e => e.expand ops n
      | none => if ops.contains n then some [n] else none
    match expanded with
    | some os => allowed := allowed ++ os
    | none => throw s!"`{n}` is neither an operation of `{svc}` nor a group it defines"
  let list := Spec.Value.render (.list (allowed.eraseDups.map .str))
  pure s!"reject if request_service({Spec.quote svc}), operation($op), !{list}.contains($op);"

/-- Compile narrowings to checks. -/
def compile (registry : Service.Registry) (lines : List String) :
    Except String (List Builder.Check) := do
  let mut checks : List Builder.Check := []
  for l in lines do
    let src ← toDatalog registry l
    match Parser.parseBlock src with
    | .ok b => checks := checks ++ b.checks
    | .error e => throw s!"the narrowing `{l}` did not compile: {e}"
  pure checks

end Narrow
end Kleis
