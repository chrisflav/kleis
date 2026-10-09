import Kleis.Service.Registry
import Kleis.Token.Issue
import Kleis.Policy.Authorize

/-!
# Which grant decides

A token may name more than one grant.  That is how one bearer reaches two
services on one token, and how one service is reached on two credentials — a
bot's installation token for its own fork, a person's token for the upstream it
opens pull requests on.

## One grant at a time

The grants a token names are tried *one at a time*, in the order the token
names them, and the first that allows the request is the one that decides it
and whose credential is spent.  They are never merged into one authorizer.

Merging would be the friendlier semantics and is the wrong one: a check in one
grant would constrain requests the other grant was written for, and a rule in
one could derive a fact that satisfied a check in the other — so what a pair of
grants allowed would be something neither author wrote.  Kept apart, each grant
means exactly what its file says, and the only thing naming two of them adds is
a second chance.  Which grant decided, and so which credential went out, is in
the audit record.

The token's own blocks apply to every attempt.  An attenuation narrows the
token, not one of its grants.
-/

namespace Kleis
namespace Policy

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- Why a request never reached a policy decision. -/
inductive Rejection where
  /-- No manifest claims the host. -/
  | unknownHost (host : String)
  /-- The token names grants nobody has. -/
  | unknownGrant (names : List String)
  /-- The token names no grant at all. -/
  | noGrant
  /-- None of the token's grants is for the service the host belongs to. -/
  | wrongService (grants : List String) (service host : String)
  /-- The credential the deciding grant spends is not installed. -/
  | noCredential (name : String)

/-- Describe a rejection. -/
def Rejection.toString : Rejection → String
  | .unknownHost h => s!"no service manifest claims `{h}`"
  | .unknownGrant [n] => s!"the token names the grant `{n}`, which is not configured"
  | .unknownGrant ns =>
    s!"the token names the grants {", ".intercalate (ns.map (s!"`{·}`"))}, none of which is configured"
  | .noGrant => "the token names no grant"
  | .wrongService [g] s h =>
    s!"the grant `{g}` is not for the service `{s}`, which is what claims `{h}`"
  | .wrongService gs s h =>
    s!"none of the token's grants ({", ".intercalate gs}) is for the service `{s}`, \
      which is what claims `{h}`"
  | .noCredential n => s!"the credential `{n}` is not installed"

/-- The grants a token may be decided by for one service, in the token's order. -/
def candidates (registry : Service.Registry) (token : Biscuit) (manifest : Service.Manifest)
    (host : String) : Except Rejection (List Grant) := do
  let names := Token.grantsOf token
  if names.isEmpty then throw .noGrant
  let known := names.filterMap registry.grant?
  if known.isEmpty then throw (.unknownGrant names)
  match known.filter (·.service == manifest.name) with
  | [] => throw (.wrongService (known.map (·.name)) manifest.name host)
  | gs => pure gs

/-- What deciding among several grants came to. -/
structure Choice where
  /-- The grant whose outcome this is: the one that allowed, or the first one
  tried when none did. -/
  grant : Grant
  /-- That grant's outcome. -/
  outcome : Outcome
  /-- Every grant that was tried and refused, with why, in order. -/
  refusals : List (Grant × Outcome)

/-- What was decided, for the audit log and the client: the grant that allowed the request, or
why each grant refused it when there was more than one. -/
def Choice.reason (c : Choice) : String :=
  if c.outcome.allowed then s!"allowed by grant `{c.grant.name}`, " ++ c.outcome.reason
  else match c.refusals with
  | [] => c.outcome.reason
  | [(_, o)] => o.reason
  | rs =>
    "no grant the token names allows this:\n" ++
      String.join (rs.map fun (g, o) =>
        s!"grant `{g.name}`: " ++ o.reason ++ (if o.reason.endsWith "\n" then "" else "\n"))

/-- Try each grant in turn; the first to allow decides.  The list must not be
empty, which `candidates` guarantees. -/
def choose (grants : List Grant) (input : Grant → Input) : Choice :=
  let rec go (rest : List Grant) (refusals : List (Grant × Outcome)) : Choice :=
    match rest with
    | [] =>
      match refusals.reverse with
      | (g, o) :: _ => { grant := g, outcome := o, refusals := refusals.reverse }
      | [] => { grant := default, outcome := run (input default), refusals := [] }
    | g :: gs =>
      let o := run (input g)
      if o.allowed then { grant := g, outcome := o, refusals := refusals.reverse }
      else go gs ((g, o) :: refusals)
  go grants []

end Policy
end Kleis
