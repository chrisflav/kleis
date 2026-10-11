import Kleis.Service.Registry
import Kleis.Token.Revocation

/-!
# Token cards, and what a sandbox needs

A **card** is plain text telling the bearer of a token what it may do, generated from how the
token was made: the specs it names, rendered in their extensions' words; the facts its issuer
stated about the task, where an extension knows how to say them; its expiry; and the narrowings
it was made with. It is written for an agent to read at the start of a task, and served at
`/.kleis/v1/card` for the bearer to read again whenever it is unsure.

A card describes; it does not decide. What decides is the grants the card was rendered from,
so the card is generated from those same grants and never from anything a bearer could add.
Where it cannot say a thing in prose — raw `datalog` in a spec, a grant file a spec includes —
it quotes the datalog rather than claim more precision than it has.

**Setup** is what a sandbox needs to use the token with ordinary tools: environment variables
and files from each extension the token reaches, with `{host}` and `{account}` filled per
account. None of it is secret: where a client insists on a credential, the extension supplies a
placeholder kleis strips and replaces.
-/

namespace Kleis
namespace Card

open LeanBiscuit
open LeanBiscuit.Token (Biscuit)

/-- The authority block's facts, as predicate names and their terms rendered as text. -/
def authorityFacts (token : Biscuit) : List (String × List String) :=
  match token.blocks.head? with
  | none => []
  | some authority =>
    authority.facts.filterMap fun f =>
      match Builder.Predicate.convertFrom token.symbols f.predicate with
      | .ok p => some (p.name, p.terms.map fun t => match t with
          | .str s => s
          | .integer n => toString n
          | .bool b => if b then "true" else "false"
          | .date d => toString d
          | _ => "…")
      | .error _ => none

/-- Fill `{0}`, `{1}` … in a phrase with a fact's terms. -/
def fillTerms (template : String) (terms : List String) : String :=
  (List.range terms.length).foldl (fun acc i =>
    acc.replace s!"\{{i}}" (terms.getD i "")) template

/-- One account a token reaches: its service, its credential, the hosts it is spent on. -/
structure Reach where
  service : String
  credential : Option String
  hosts : List String
  deriving Inhabited

/-- Everything a token reaches, by account: each compiled account of each spec it names, and
each grant it names or a spec includes. -/
def reaches (registry : Service.Registry) (token : Biscuit) : List Reach :=
  let hostsOf (svc : String) : List String :=
    ((registry.manifest? svc).map (·.credential.hosts)).getD []
  let fromSpecs := (Token.specsOf token).filterMap registry.spec? |>.flatMap fun s =>
    s.accounts.map (fun a =>
      ({ service := a.record.service, credential := some a.record.name
         hosts := if a.record.hosts.isEmpty then hostsOf a.record.service else a.record.hosts } : Reach))
    ++ s.includes.filterMap fun g => (registry.grant? g).map fun g =>
      { service := g.service, credential := g.credential, hosts := hostsOf g.service }
  let fromGrants := (Token.grantsOf token).filterMap registry.grant? |>.map fun g =>
    ({ service := g.service, credential := g.credential, hosts := hostsOf g.service } : Reach)
  fromGrants ++ fromSpecs

private def testPhrase : Spec.Test → String
  | .is v => s!"is {Spec.Value.render v}"
  | .isIn vs => s!"is one of {Spec.Value.render (.list vs)}"
  | .startsWith s => s!"starts with {Spec.quote s}"
  | .endsWith s => s!"ends with {Spec.quote s}"
  | .matches s => s!"matches {Spec.quote s}"
  | .compare op n => s!"is {op} {n}"

private def atomPhrase (e : Service.Extension) (a : Spec.Atom) : String :=
  let field := ((e.field? a.field).map (·.phrase)).getD a.field
  match a.quant with
  | some .all => s!"every {field} {testPhrase a.test} (and there is at least one)"
  | some .any => s!"some {field} {testPhrase a.test}"
  | none => s!"{field} {testPhrase a.test}"

private def fmtTime (secs : Nat) : String :=
  -- Days since the epoch to a civil date (Howard Hinnant's algorithm), UTC.
  let days := secs / 86400
  let rem := secs % 86400
  let z : Int := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := if m ≤ 2 then y + 1 else y
  let pad (n : Int) : String := if n < 10 then s!"0{n}" else toString n
  s!"{y}-{pad m}-{pad d} {pad (rem / 3600)}:{pad ((rem % 3600) / 60)} UTC"

/-- Render a token's card. `records` are the issued records of the token's blocks, which
carry its expiry and the narrowings it was made with. -/
def render (registry : Service.Registry) (token : Biscuit) (records : List Token.IssuedRecord) :
    String := Id.run do
  let mut out : Array String := #[]
  let specs := (Token.specsOf token).filterMap registry.spec?
  for s in specs do
    let desc := if s.description.isEmpty then "" else s!": {s.description}"
    out := out.push s!"This token acts as \"{s.name}\"{desc}"
  if specs.isEmpty then
    out := out.push "This token is for the grants it names, below."
  let expiries : List Nat := (records.map (·.expires)).filter (· > 0)
  if let some e := expiries.min? then
    out := out.push s!"It expires {fmtTime e}."
  let facts := authorityFacts token
  -- One section per account of every spec.
  for s in specs do
    for a in s.accounts do
      let e := a.extension
      let label := if a.record.hosts.isEmpty then a.record.name
        else s!"{a.record.name} on {", ".intercalate a.record.hosts}"
      let client := if e.client.isEmpty then "" else s!" ({e.client})"
      out := out.push ""
      out := out.push s!"{e.display} — {label}{client}"
      for r in a.account.rules do
        match r with
        | .allow al =>
          let what := ", ".intercalate (al.ops.map e.phraseOf)
          let conds := al.conds.map (atomPhrase e)
          let when := if conds.isEmpty then "" else s!", only if {" and ".intercalate conds}"
          out := out.push s!"  • {what}{when}"
        | .datalog src _ =>
          out := out.push "  • also, as written in datalog:"
          for l in (src.splitOn "\n").filter (fun l => !(Str.trim l).isEmpty) do
            out := out.push s!"      {Str.trim l}"
      out := out.push s!"  • nothing else on this account"
  -- Grants the token names, or its specs include: described by what their extension can
  -- say about the task, and quoted.
  let grantNames := Token.grantsOf token ++ specs.flatMap (·.includes)
  for g in (grantNames.eraseDups.filterMap registry.grant?) do
    let e? := registry.extension? g.service
    let display := (e?.map (·.display)).getD g.service
    out := out.push ""
    out := out.push s!"{display} — under the grant `{g.name}`{((e?.map (fun e => if e.client.isEmpty then "" else s!" ({e.client})")).getD "")}"
    if let some e := e? then
      for (pred, phrase) in e.factPhrases do
        for (name, terms) in facts do
          if name == pred then out := out.push s!"  • {fillTerms phrase terms}"
    out := out.push "  • what it allows, as written:"
    let datalog := match Toml.parse g.source with
      | .ok j => (j.str? "datalog").getD ""
      | .error _ => ""
    for l in (datalog.splitOn "\n") do
      let t := (l.trimAsciiEnd).toString
      if !(Str.trim t).isEmpty && !(Str.trim t).startsWith "//" then out := out.push s!"      {t}"
  -- Narrowings, from the records of the blocks that made them.
  let narrowings := records.flatMap (·.narrowings)
  if !narrowings.isEmpty then
    out := out.push ""
    out := out.push s!"This copy is narrowed further: {"; ".intercalate narrowings}."
  out := out.push ""
  out := out.push "Anything else is refused with HTTP 403, and the response says which rule refused it."
  return "\n".intercalate out.toList ++ "\n"

/-- A file a sandbox is to be given. -/
structure File where
  path : String
  mode : Option String
  content : String
  deriving Inhabited

/-- Environment and files for a token, from every extension it reaches. Paths are relative to
the sandbox user's home, and checked again after placeholders are filled. -/
def setup (registry : Service.Registry) (token : Biscuit) :
    Except String (List (String × String) × List File) := do
  let rs := reaches registry token
  let services := (rs.map (·.service)).eraseDups
  let mut env : List (String × String) := []
  let mut files : List File := []
  for svc in services do
    let some e := registry.extension? svc | continue
    for (k, v) in e.env do
      match env.find? (·.1 == k) with
      | some (_, v') => if v' != v then throw s!"two extensions set `{k}` differently"
      | none => env := env ++ [(k, v)]
    let accounts := rs.filter (·.service == svc)
    for f in e.files do
      let fill (host account : String) (s : String) : String :=
        (s.replace "{host}" host).replace "{account}" account
      let instances : List (String × String) :=
        if f.perAccount then accounts.flatMap fun r =>
          r.hosts.map fun h => (h, r.credential.getD "")
        else match accounts.head? with
          | some r => [(r.hosts.headD "", r.credential.getD "")]
          | none => []
      for (h, acct) in instances do
        let path := fill h acct f.path
        if !Service.safeRelativePath path then
          throw s!"the setup file `{path}` of `{svc}` is not a path relative to the home directory"
        if !(files.any (·.path == path)) then
          files := files ++ [{ path, mode := f.mode, content := fill h acct f.content }]
  pure (env, files)

end Card
end Kleis
