import Kleis.Service.Extension
import Kleis.Policy.Grant
import Kleis.Credential.Store

/-!
# Specs

A spec is a named description of what a bearer may do, written once by whoever owns the
accounts it uses, and named by tokens (`spec("secretary")` in an authority block).

```
spec secretary
  description "Reads and files Christian's mail and keeps his calendar."
  max_ttl 24h

  account mail/christian
    allow read, flag, move
    allow send where recipient all ends_with "@merten.dev"

  account caldav/christian@dav.example.org
    allow read
    allow write, delete where path starts_with "calendars/christian/personal/"
```

It is compiled, when the configuration is loaded, into one ordinary grant per `account` block
(`Policy.Grant`), so everything DESIGN §4 says about grants holds of it unchanged. The language
is only a way of writing grants: shorter, checked against the extension's vocabulary so that a
typo is a load error rather than a policy that allows nothing, and structured enough for a card
(`Kleis.Card`) to say back in prose what it allows. `kleis spec compile` prints the datalog.

## Grammar

```
spec   ::= "spec" NAME NL field* block*
field  ::= "description" STRING | "max_ttl" DURATION
block  ::= "account" CREDENTIAL NL rule*        -- one grant, spending that credential
         | "grant" GRANT                        -- an existing grant, included as it is
rule   ::= "allow" OP ("," OP)* ("where" atom ("and" atom)*)?
         | "datalog" "'''" … "'''"              -- raw rules and checks, for what the rest cannot say
atom   ::= FIELD test | FIELD ("all" | "any") test
test   ::= "is" VALUE | "in" LIST | "starts_with" STRING | "ends_with" STRING
         | "matches" STRING | ("<" | "<=" | ">" | ">=") INT
```

`#` starts a comment. A rule belongs to the `account` above it and is indented further.

## Meaning

`allow OPS` admits a request whose operation is one of `OPS` — a manifest operation, or a group
the extension defines. `where` narrows the line: every atom must hold. A single-valued field's
test applies to its value, and a request without one fails it. A multi-valued field's test is
quantified: `all` — at least one value, and every value passes; `any` — some value passes.
Lines are alternatives; what no line admits is refused.

`all` is compiled as a `reject if` (biscuit has no negation in rule bodies, and a check over one
fact per value cannot say "every"). A reject applies to the whole grant, not one line, so an
`all` condition may only stand on a line whose operations no other line of the block names.
-/

namespace Kleis
namespace Spec

open LeanBiscuit

/-- A value in a test. -/
inductive Value where
  | str (s : String)
  | int (n : Int)
  | bool (b : Bool)
  | list (vs : List Value)
  deriving Repr, Inhabited, BEq

/-- A test applied to a field's value. -/
inductive Test where
  | is (v : Value)
  | isIn (vs : List Value)
  | startsWith (s : String)
  | endsWith (s : String)
  | matches (s : String)
  | compare (op : String) (n : Int)
  deriving Repr, Inhabited

/-- How a test on a multi-valued field is quantified. -/
inductive Quant where
  | all
  | any
  deriving Repr, Inhabited, BEq

/-- One condition. -/
structure Atom where
  field : String
  quant : Option Quant
  test : Test
  deriving Repr, Inhabited

/-- One `allow` line. -/
structure Allow where
  ops : List String
  conds : List Atom
  line : Nat
  deriving Repr, Inhabited

/-- A rule in an account block. -/
inductive Rule where
  | allow (a : Allow)
  | datalog (source : String) (line : Nat)
  deriving Repr, Inhabited

/-- An `account` block. -/
structure Account where
  credential : String
  rules : List Rule
  line : Nat
  deriving Repr, Inhabited

/-- A spec, as written. -/
structure Source where
  name : String
  description : String
  maxTtl : Option Nat
  accounts : List Account
  includes : List String
  deriving Repr, Inhabited

/-! ## Lexing -/

/-- A token on one line. -/
inductive Tok where
  | word (s : String)
  | str (s : String)
  | comma
  | lbrack
  | rbrack
  deriving Repr, BEq, Inhabited

private def isWordChar (c : Char) : Bool :=
  !c.isWhitespace && c != ',' && c != '[' && c != ']' && c != '"' && c != '#'

/-- Split one line into tokens, dropping a trailing comment. -/
partial def lexLine (line : String) : Except String (List Tok) :=
  let rec go (cs : List Char) (acc : Array Tok) : Except String (List Tok) :=
    match cs with
    | [] => .ok acc.toList
    | c :: rest =>
      if c.isWhitespace then go rest acc
      else if c == '#' then .ok acc.toList
      else if c == ',' then go rest (acc.push .comma)
      else if c == '[' then go rest (acc.push .lbrack)
      else if c == ']' then go rest (acc.push .rbrack)
      else if c == '"' then
        let rec str (cs : List Char) (s : String) : Except String (String × List Char) :=
          match cs with
          | [] => .error "a string is not closed"
          | '"' :: rest => .ok (s, rest)
          | '\\' :: '"' :: rest => str rest (s.push '"')
          | '\\' :: '\\' :: rest => str rest (s.push '\\')
          | '\\' :: 'n' :: rest => str rest (s.push '\n')
          | '\\' :: _ => .error "a string has an unknown escape; use \\\\, \\\" or \\n"
          | c :: rest => str rest (s.push c)
        match str rest "" with
        | .error e => .error e
        | .ok (s, rest) => go rest (acc.push (.str s))
      else
        let word := (c :: rest).takeWhile isWordChar
        go ((c :: rest).drop word.length) (acc.push (.word (String.ofList word)))
  go line.toList #[]

/-! ## Parsing -/

private def indentOf (line : String) : Nat := (line.toList.takeWhile (· == ' ')).length

private def isName (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- Parse a value: a string, an integer, a boolean, or a list of those. -/
private partial def parseValue : List Tok → Except String (Value × List Tok)
  | .str s :: rest => .ok (.str s, rest)
  | .word "true" :: rest => .ok (.bool true, rest)
  | .word "false" :: rest => .ok (.bool false, rest)
  | .word w :: rest =>
    match w.toInt? with
    | some n => .ok (.int n, rest)
    | none => .error s!"`{w}` is not a value; strings are quoted"
  | .lbrack :: rest =>
    let rec items (ts : List Tok) (acc : List Value) : Except String (Value × List Tok) :=
      match ts with
      | .rbrack :: rest => .ok (.list acc.reverse, rest)
      | _ => do
        let (v, rest) ← parseValue ts
        match rest with
        | .comma :: rest => items rest (v :: acc)
        | .rbrack :: rest => .ok (.list (v :: acc).reverse, rest)
        | _ => .error "a list is `[a, b, c]`"
    items rest []
  | _ => .error "expected a value"

private def parseAtom (ts : List Tok) : Except String (Atom × List Tok) := do
  let (field, ts) ← match ts with
    | .word f :: rest => pure (f, rest)
    | _ => throw "a condition starts with a field name"
  let (quant, ts) := match ts with
    | .word "all" :: rest => (some Quant.all, rest)
    | .word "any" :: rest => (some Quant.any, rest)
    | _ => (none, ts)
  let (test, ts) ← match ts with
    | .word "is" :: rest => do let (v, r) ← parseValue rest; pure (Test.is v, r)
    | .word "in" :: rest => do
      let (v, r) ← parseValue rest
      match v with
      | .list vs => pure (Test.isIn vs, r)
      | _ => throw "`in` takes a list"
    | .word "starts_with" :: .str s :: rest => pure (Test.startsWith s, rest)
    | .word "ends_with" :: .str s :: rest => pure (Test.endsWith s, rest)
    | .word "matches" :: .str s :: rest => pure (Test.matches s, rest)
    | .word op :: rest =>
      if ["<", "<=", ">", ">="].contains op then do
        let (v, r) ← parseValue rest
        match v with
        | .int n => pure (Test.compare op n, r)
        | _ => throw s!"`{op}` compares with an integer"
      else throw s!"`{op}` is not a test; use is, in, starts_with, ends_with, matches, <, <=, >, >="
    | _ => throw s!"the condition on `{field}` has no test"
  pure ({ field, quant, test }, ts)

private partial def parseAllow (ts : List Tok) (line : Nat) : Except String Allow := do
  let rec ops (ts : List Tok) (acc : List String) : Except String (List String × List Tok) :=
    match ts with
    | .word o :: .comma :: rest => ops rest (o :: acc)
    | .word o :: rest => .ok ((o :: acc).reverse, rest)
    | _ => .error "`allow` names at least one operation"
  let (os, ts) ← ops ts []
  match ts with
  | [] => pure { ops := os, conds := [], line }
  | .word "where" :: rest =>
    let rec conds (ts : List Tok) (acc : List Atom) : Except String (List Atom) := do
      let (a, rest) ← parseAtom ts
      match rest with
      | [] => pure (a :: acc).reverse
      | .word "and" :: rest => conds rest (a :: acc)
      | _ => throw "conditions are joined with `and`"
    pure { ops := os, conds := ← conds rest [], line }
  | _ => throw "after the operations comes `where`, or nothing"

private def parseDurationTok (s : String) : Except String Nat :=
  match Policy.parseDuration? s with
  | some n => if n == 0 then .error "a duration must be positive" else .ok n
  | none => .error s!"`{s}` is not a duration such as 24h"

/-- Parse a spec file. -/
def parse (text : String) : Except String Source := do
  let lines := (text.splitOn "\n").toArray
  let mut i := 0
  let mut name : Option String := none
  let mut description := ""
  let mut maxTtl : Option Nat := none
  let mut accounts : Array Account := #[]
  let mut includes : Array String := #[]
  -- The account being filled, and its indentation.
  let mut current : Option (Account × Nat) := none
  while i < lines.size do
    let raw := lines[i]!
    let lineNo := i + 1
    i := i + 1
    let ind := indentOf raw
    let toks ← match lexLine raw with
      | .ok t => pure t
      | .error e => throw s!"line {lineNo}: {e}"
    if toks.isEmpty then continue
    let here (msg : String) : String := s!"line {lineNo}: {msg}"
    -- A rule line must be inside the account it belongs to.
    let inAccount := match current with
      | some (_, ai) => ind > ai
      | none => false
    match toks with
    | [.word "spec", .word n] =>
      if name.isSome then throw (here "a file holds one spec")
      if !isName n then throw (here s!"`{n}` is not a spec name")
      name := some n
    | .word "spec" :: _ => throw (here "`spec NAME`")
    | _ =>
      if name.isNone then throw (here "a spec file starts with `spec NAME`")
      match toks with
      | [.word "description", .str d] =>
        if current.isSome then throw (here "`description` belongs before the first account")
        description := d
      | [.word "max_ttl", .word d] =>
        if current.isSome then throw (here "`max_ttl` belongs before the first account")
        match parseDurationTok d with
        | .ok n => maxTtl := some n
        | .error e => throw (here e)
      | [.word "account", .word c] =>
        if let some (a, _) := current then accounts := accounts.push a
        current := some ({ credential := c, rules := [], line := lineNo }, ind)
      | [.word "grant", .word g] =>
        if let some (a, _) := current then accounts := accounts.push a
        current := none
        includes := includes.push g
      | .word "allow" :: rest =>
        let some (a, ai) := current | throw (here "`allow` belongs to an `account`")
        if !inAccount then throw (here "`allow` is indented under its `account`")
        match parseAllow rest lineNo with
        | .ok al => current := some ({ a with rules := a.rules ++ [.allow al] }, ai)
        | .error e => throw (here e)
      | .word "datalog" :: _ =>
        let some (a, ai) := current | throw (here "`datalog` belongs to an `account`")
        if !inAccount then throw (here "`datalog` is indented under its `account`")
        -- The block runs from the first `'''` to the next, across lines.
        let afterKw := (raw.splitOn "datalog").drop 1 |> "datalog".intercalate
        let some (_, opened) := Str.splitOnce? afterKw "'''"
          | throw (here "`datalog '''…'''`")
        let mut body := opened
        let mut closed := false
        if let some (inner, _) := Str.splitOnce? body "'''" then
          body := inner
          closed := true
        while !closed && i < lines.size do
          let l := lines[i]!
          i := i + 1
          match Str.splitOnce? l "'''" with
          | some (inner, _) => body := body ++ "\n" ++ inner; closed := true
          | none => body := body ++ "\n" ++ l
        if !closed then throw (here "the `datalog` block is not closed with '''")
        current := some ({ a with rules := a.rules ++ [.datalog body lineNo] }, ai)
      | _ => throw (here "expected description, max_ttl, account, grant, allow or datalog")
  if let some (a, _) := current then accounts := accounts.push a
  let some n := name | throw "the file holds no spec"
  pure { name := n, description, maxTtl, accounts := accounts.toList, includes := includes.toList }

/-! ## Compilation -/

/-- A datalog string literal. -/
def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n") ++ "\""

/-- A value as datalog. -/
partial def Value.render : Value → String
  | .str s => quote s
  | .int n => toString n
  | .bool b => if b then "true" else "false"
  | .list vs => "[" ++ ", ".intercalate (vs.map Value.render) ++ "]"

private def Value.typeName : Value → String
  | .str _ => "string"
  | .int _ => "int"
  | .bool _ => "bool"
  | .list _ => "list"

/-- The expression a test makes of a variable. -/
def Test.render (t : Test) (v : String) : String :=
  match t with
  | .is x => s!"{v} == {x.render}"
  | .isIn xs => s!"{(Value.list xs).render}.contains({v})"
  | .startsWith s => s!"{v}.starts_with({quote s})"
  | .endsWith s => s!"{v}.ends_with({quote s})"
  | .matches s => s!"{v}.matches({quote s})"
  | .compare op n => s!"{v} {op} {n}"

/-- The values a test compares with, for type checking. -/
private def Test.values : Test → List Value
  | .is x => [x]
  | .isIn xs => xs
  | .startsWith s | .endsWith s | .matches s => [.str s]
  | .compare _ n => [.int n]

/-- What a compiled spec needs to know about the world. -/
structure Env where
  /-- Extensions by service, with their manifests. -/
  extensions : List (Service.Extension × Service.Manifest)
  /-- Every credential record, declared and installed. -/
  credentials : Array Credential.Record
  /-- The grants loaded from files, which `grant` may include. -/
  grants : Array Policy.Grant

/-- A compiled account block: the grant, and what a card needs to describe it. -/
structure CompiledAccount where
  account : Account
  record : Credential.Record
  extension : Service.Extension
  grant : Policy.Grant
  deriving Inhabited

/-- A spec, compiled. -/
structure Spec where
  name : String
  description : String
  maxTtl : Nat
  accounts : List CompiledAccount
  /-- Grants included by name, with `grant(name)` asserted for them (`Kleis.Policy.Select`). -/
  includes : List String
  /-- SHA-256 of the source, hex, recorded with every decision. -/
  version : String
  deriving Inhabited

/-- The compiled grants' names: `<spec>/<credential>`. -/
def grantName (spec credential : String) : String := s!"{spec}/{credential}"

/-- The datalog of one account's grant. -/
def compileAccount (spec : String) (a : Account) (record : Credential.Record)
    (ext : Service.Extension) (manifestOps : List String) : Except String String := do
  let here (line : Nat) (msg : String) : String := s!"line {line}: {msg}"
  let mut lines : Array String := #[s!"check if spec({quote spec});"]
  if !record.hosts.isEmpty then
    lines := lines.push
      s!"check if request_host($h), {(Value.list (record.hosts.map .str)).render}.contains($h);"
  let allows := a.rules.filterMap fun r => match r with
    | .allow al => some al
    | _ => none
  -- Expand every line's operations, refusing unknown names.
  let mut expanded : Array (Allow × List String) := #[]
  for al in allows do
    let mut ops : List String := []
    for o in al.ops do
      match ext.expand manifestOps o with
      | some os => ops := ops ++ os
      | none => throw (here al.line
          s!"`{o}` is neither an operation of `{ext.service}` nor a group it defines")
    expanded := expanded.push (al, ops.eraseDups)
  let mut rejects : Array String := #[]
  for h : n in [0:expanded.size] do
    let (al, ops) := expanded[n]
    let opsTest := s!"operation($op), {(Value.list (ops.map .str)).render}.contains($op)"
    let mut body : Array String := #[opsTest]
    for h' : k in [0:al.conds.length] do
      let c := al.conds[k]
      let some f := ext.field? c.field
        | throw (here al.line s!"`{c.field}` is not a field of `{ext.service}`; it has {(ext.fields.map (·.name))}")
      for v in c.test.values do
        if v.typeName != f.type then
          throw (here al.line s!"`{c.field}` is a {f.type}, and the test compares with a {v.typeName}")
      match c.test with
      | .startsWith _ | .endsWith _ | .matches _ =>
        if f.type != "string" then throw (here al.line s!"`{c.field}` is not a string")
      | .compare _ _ =>
        if f.type != "int" then throw (here al.line s!"`{c.field}` is not an integer")
      | _ => pure ()
      let var := s!"$c{k}"
      match f.multi, c.quant with
      | false, some _ => throw (here al.line s!"`{c.field}` has one value; `all`/`any` is for fields with several")
      | true, none => throw (here al.line s!"`{c.field}` has several values; say `{c.field} all …` or `{c.field} any …`")
      | false, none | true, some .any =>
        body := body.push s!"{f.fact}({var}), {c.test.render var}"
      | true, some .all =>
        -- At least one value here; that every value passes is the reject's.
        body := body.push s!"{f.fact}({var})"
        let others := (List.range expanded.size).filterMap fun m =>
          if m == n then none else expanded[m]?
        for ((other : Allow), (otherOps : List String)) in others do
          if otherOps.any ops.contains then
            throw (here al.line s!"an `all` condition's operations may not appear on another line (line {other.line}): a reject applies to the whole account")
        rejects := rejects.push s!"reject if {opsTest}, {f.fact}($r), !({c.test.render "$r"});"
    lines := lines.push s!"allowed({n}) <- {", ".intercalate body.toList};"
  if allows.isEmpty then
    -- An account with only raw datalog decides with that datalog.
    pure ()
  else
    lines := lines.push "check if allowed($x);"
  lines := lines ++ rejects
  for r in a.rules do
    if let .datalog src _ := r then lines := lines.push src
  lines := lines.push "allow if true;"
  pure ("\n".intercalate lines.toList)

/-- A TOML basic string. -/
private def tomlString (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- Compile a parsed spec against the world. -/
def compile (src : Source) (text : String) (env : Env) : Except String Spec := do
  let some maxTtl := src.maxTtl | throw "a spec needs `max_ttl`"
  let mut accounts : Array CompiledAccount := #[]
  let mut seen : List String := []
  for a in src.accounts do
    let here (msg : String) : String := s!"line {a.line}: {msg}"
    if seen.contains a.credential then throw (here s!"`{a.credential}` has two account blocks")
    seen := a.credential :: seen
    let some record := env.credentials.find? (·.name == a.credential)
      | throw (here s!"no credential `{a.credential}` is installed or declared")
    let some (ext, manifest) := env.extensions.find? (·.1.service == record.service)
      | throw (here s!"`{a.credential}` is for `{record.service}`, whose extension is not enabled")
    if ext.dynamicHosts && record.hosts.isEmpty then
      throw (here s!"`{a.credential}` is for `{record.service}`, whose servers vary, so it must name its `hosts`")
    let datalog ← compileAccount src.name a record ext (Service.Manifest.operations manifest)
    if (datalog.splitOn "'''").length > 1 then throw (here "the compiled datalog may not contain '''")
    let toml := s!"name = {tomlString (grantName src.name a.credential)}\n"
      ++ s!"service = {tomlString record.service}\n"
      ++ s!"credential = {tomlString a.credential}\n"
      ++ s!"max_lifetime = \"{maxTtl}s\"\n"
      ++ s!"datalog = '''\n{datalog}\n'''\n"
    let grant ← match Policy.Grant.ofToml toml with
      | .ok g => pure g
      | .error e => throw (here s!"the compiled grant does not load: {e}")
    accounts := accounts.push { account := a, record, extension := ext, grant }
  for g in src.includes do
    if !(env.grants.any (·.name == g)) then throw s!"the spec includes the grant `{g}`, which is not configured"
  pure { name := src.name, description := src.description, maxTtl
         accounts := accounts.toList, includes := src.includes
         version := Bytes.toHex (Sha256.hash (Bytes.ofString text)) }

/-- Parse and compile. -/
def load (text : String) (env : Env) : Except String Spec := do
  compile (← parse text) text env

end Spec
end Kleis
