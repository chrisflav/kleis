import Kleis.Wire.Json

/-!
# The GraphQL decoder

A GraphQL request is JSON — `{"query": "…", "variables": {…}}` — and the JSON
decoder reads it well enough.  What it cannot say is the one thing a policy most
often needs: whether the request *changes* anything.  That is in the query
string, as the keyword in front of each operation, and datalog has no way to
take a string apart.

So this decoder reads the request as JSON and then reads the document for its
operations, adding them under `$operations`:

```
body(["$operations", 0, "type"], "mutation");
body(["$operations", 0, "name"], "CreatePullRequest");
```

A `$operations` key the client sent itself is replaced, not merged.

## What it does not do

It does not parse GraphQL.  It finds the top-level definitions — skipping
strings, block strings, comments and balanced brackets — and reads the keyword
in front of each.  That is enough to answer "is any operation in this document a
mutation", and it is deliberately not enough to answer "which fields does it
touch": a policy that tried to allow some mutations by their field names would
be a policy over a language this decoder does not understand.  The useful
policy is the coarse one — queries allowed, mutations refused — and that this
supports exactly.

A document it cannot read is `opaque`, which under a configured decoder is
`body_undecodable` and refused by the authorizer's guard.  So is a batch (a JSON
array of requests): nothing is lost by refusing it, and reading only the first
would let the second through unseen.
-/

namespace Kleis
namespace Wire

open LeanBiscuit (Bytes)
open LeanBiscuit.Datalog (Value)

namespace GraphQL

/-- An operation found at the top level of a document. -/
structure Operation where
  /-- `query`, `mutation` or `subscription`. -/
  kind : String
  /-- Its name, or empty for an anonymous one. -/
  name : String
  deriving Repr, BEq, Inhabited

private def isNameStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Skip whitespace, commas, the byte-order mark and `#` comments. -/
private def skipIgnored (s : List Char) : List Char :=
  let rec go (s : List Char) (fuel : Nat) : List Char :=
    match fuel, s with
    | 0, _ => s
    | _, [] => []
    | fuel + 1, c :: rest =>
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ',' || c == '\uFEFF' then
        go rest fuel
      else if c == '#' then go (rest.dropWhile (· != '\n')) fuel
      else s
  go s (s.length + 1)

/-- Skip a string whose opening quote has been consumed. -/
private def skipString : List Char → Option (List Char)
  | [] => none
  | '\\' :: _ :: rest => skipString rest
  | '"' :: rest => some rest
  | '\n' :: _ => none
  | _ :: rest => skipString rest

/-- Skip a block string whose opening `"""` has been consumed. -/
private def skipBlockString : List Char → Option (List Char)
  | [] => none
  | '\\' :: '"' :: '"' :: '"' :: rest => skipBlockString rest
  | '"' :: '"' :: '"' :: rest => some rest
  | _ :: rest => skipBlockString rest

/-- Skip a balanced bracketed group whose opening bracket has been consumed,
with `depth` brackets still open.  Strings are skipped whole, so a bracket
inside one is not counted. -/
private def skipBalanced (s : List Char) (depth : Nat) : Option (List Char) :=
  -- Fuel rather than a measure: each step consumes at least one character, so
  -- the input's length is always enough.
  let rec go (s : List Char) (depth : Nat) (fuel : Nat) : Option (List Char) :=
    if depth == 0 then some s else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match s with
      | [] => none
      | '"' :: '"' :: '"' :: rest => (skipBlockString rest).bind (go · depth fuel)
      | '"' :: rest => (skipString rest).bind (go · depth fuel)
      | '#' :: rest => go (rest.dropWhile (· != '\n')) depth fuel
      | c :: rest =>
        if c == '{' || c == '(' || c == '[' then go rest (depth + 1) fuel
        else if c == '}' || c == ')' || c == ']' then go rest (depth - 1) fuel
        else go rest depth fuel
  go s depth (s.length + 1)

/-- Read a name. -/
private def readName (s : List Char) : Option (String × List Char) :=
  match s with
  | c :: _ =>
    if isNameStart c then
      let name := s.takeWhile isNameChar
      some (String.ofList name, s.drop name.length)
    else none
  | [] => none

/-- Skip a definition's header — name, variable definitions, type condition,
directives — and its selection set, returning what follows it. -/
private def skipDefinitionBody (s : List Char) (fuel : Nat) : Option (List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match skipIgnored s with
    | '{' :: rest => skipBalanced rest 1
    | '(' :: rest => (skipBalanced rest 1).bind (skipDefinitionBody · fuel)
    | '@' :: rest => (readName rest).bind fun (_, more) => skipDefinitionBody more fuel
    | ':' :: rest => skipDefinitionBody rest fuel
    | '$' :: rest => skipDefinitionBody rest fuel
    | '!' :: rest => skipDefinitionBody rest fuel
    | '[' :: rest => (skipBalanced rest 1).bind (skipDefinitionBody · fuel)
    | '=' :: rest => skipDefinitionBody rest fuel
    | '"' :: '"' :: '"' :: rest => (skipBlockString rest).bind (skipDefinitionBody · fuel)
    | '"' :: rest => (skipString rest).bind (skipDefinitionBody · fuel)
    | other =>
      match readName other with
      | some (_, more) => skipDefinitionBody more fuel
      | none =>
        -- A number in a default value, which no other branch reads.
        match other with
        | c :: more => if c.isDigit || c == '-' || c == '.' then skipDefinitionBody more fuel
                       else none
        | [] => none

/-- The operations defined at the top level of a document, or `none` if it is
not one this reader can follow. -/
def operations (document : String) : Option (List Operation) :=
  let rec go (s : List Char) (acc : List Operation) (fuel : Nat) : Option (List Operation) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match skipIgnored s with
      | [] => some acc.reverse
      | '{' :: rest =>
        -- The query shorthand: a bare selection set is an anonymous query.
        (skipBalanced rest 1).bind fun more => go more (⟨"query", ""⟩ :: acc) fuel
      | other => do
        let (keyword, more) ← readName other
        if keyword == "query" || keyword == "mutation" || keyword == "subscription" then
          let afterKeyword := skipIgnored more
          let (name, afterName) := match readName afterKeyword with
            | some (n, r) => (n, r)
            | none => ("", afterKeyword)
          let next ← skipDefinitionBody afterName 10000
          go next (⟨keyword, name⟩ :: acc) fuel
        else if keyword == "fragment" then
          let next ← skipDefinitionBody more 10000
          go next acc fuel
        else none
  go document.toList [] 10000

/-- Render the operations as the JSON the decoder adds. -/
def operationsJson (ops : List Operation) : Json :=
  .arr (ops.map fun o => .obj [("name", .str o.name), ("type", .str o.kind)])

end GraphQL

/-- Decode a complete GraphQL-over-HTTP request body. -/
def graphqlDecoder : PureDecoder where
  name := "graphql"
  media := #[]
  step := fun buf complete =>
    if !complete then .need (buf.size + 1)
    else match Json.parse (Bytes.toStringLossy buf) with
      | .ok (.obj fields) =>
        match fields.find? (·.1 == "query") with
        | some (_, .str document) =>
          match GraphQL.operations document with
          | some ops =>
            let kept := fields.filter (·.1 != "$operations")
            .done (Json.obj (kept ++ [("$operations", GraphQL.operationsJson ops)])).toValue
              buf.size
          | none => .opaque
        | _ => .opaque
      | _ => .opaque

end Wire
end Kleis
