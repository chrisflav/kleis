import Kleis.Facts.Primitive

/-!
# Flattening a body

A decoded body is emitted twice: once whole, as a single term, and once taken
apart into one fact per scalar, keyed by the path that reaches it.

```
request_body({"base": "main", "updates": [{"ref": "refs/heads/main"}]});
body(["base"], "main");
body(["updates", 0, "ref"], "refs/heads/main");
body_kind(["updates"], "array");
body_len(["updates"], 1);
```

The flattening is what makes a service-independent policy language possible at
all.  Datalog cannot unnest an array into facts, so a whole-body term supports
only closures over constant predicates — enough for "every element satisfies
this fixed test", useless for joining each element against a rule.  One fact
per scalar turns an array index into an ordinary variable:

```
ref_update($ref) <-
  body($p, $ref),
  $p.length() == 3, $p.get(0) == "updates", $p.get(2) == "ref";
```

Containers are described rather than duplicated.  Emitting a fact for every
subtree would repeat every scalar once per ancestor; `body_kind` and `body_len`
say what a rule actually needs to know about a node it is not descending into.

The whole thing is bounded, in what it emits and so in what the authorizer has
to evaluate.  Every fact is charged against `limit`: one per scalar, two per
container (its `body_kind` and its `body_len`), so a body of nothing but empty
arrays costs what its facts cost.  Nesting is bounded too, by `maxBodyDepth`.
Past either nothing is emitted but `body_truncated(true)`, and the authorizer's
preamble denies on that fact — a body too large to reason about is a refusal,
not a blind spot.
-/

namespace Kleis
namespace Facts

open LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

/-- A path into a value: string keys and array indices, outermost first. -/
abbrev Path := List Builder.Term

/-- How deeply a body's arrays and objects may nest before it is too deep to read. -/
def maxBodyDepth : Nat := 64

/-- What flattening accumulates: the leaves and the container descriptions
found so far, in reverse, and how much budget is left. -/
private structure Acc where
  /-- Scalar leaves, reversed. -/
  leaves : List (Path × Value)
  /-- Container descriptions, reversed. -/
  shapes : List (Path × String × Nat)
  /-- Remaining budget, in facts. -/
  budget : Nat
  /-- Whether the budget or the depth ran out. -/
  truncated : Bool

mutual

/-- Walk one node, `depth` containers below the top. -/
private def walk (path : Path) (depth : Nat) (v : Value) (a : Acc) : Acc :=
  if a.truncated || a.budget == 0 then { a with truncated := true } else
  -- A container costs its two facts, and may not open past the depth bound.
  let open_ (kind : String) (n : Nat) (a : Acc) : Option Acc :=
    if depth ≥ maxBodyDepth || a.budget < 2 then none
    else some { a with shapes := (path, kind, n) :: a.shapes, budget := a.budget - 2 }
  match v with
  | .array l => match open_ "array" l.length a with
    | some a => walkList path depth 0 l a
    | none => { a with truncated := true }
  | .set l => match open_ "set" l.length a with
    | some a => walkList path depth 0 l a
    | none => { a with truncated := true }
  | .map entries => match open_ "map" entries.length a with
    | some a => walkEntries path depth entries a
    | none => { a with truncated := true }
  | scalar =>
    { a with leaves := (path, scalar) :: a.leaves, budget := a.budget - 1 }

/-- Walk the elements of an array or set, indexed by position, stopping at the first that
does not fit. -/
private def walkList (path : Path) (depth i : Nat) : List Value → Acc → Acc
  | [], a => a
  | x :: xs, a =>
    if a.truncated then a else
    let a := walk (path ++ [.integer (Int.ofNat i)]) (depth + 1) x a
    walkList path depth (i + 1) xs a

/-- Walk the members of a map, stopping at the first that does not fit. -/
private def walkEntries (path : Path) (depth : Nat) : List (ValueKey × Value) → Acc → Acc
  | [], a => a
  | (k, v) :: xs, a =>
    if a.truncated then a else
    let key : Builder.Term := match k with
      | .integer i => .integer i
      | .str s => .str s
    let a := walk (path ++ [key]) (depth + 1) v a
    walkEntries path depth xs a

end

/-- The flattening of a body, or `none` if it is past the bounds. -/
private def flatten? (pred : String) (v : Value) (limit : Nat) : Option (List Fact) :=
  let a := walk [] 0 v { leaves := [], shapes := [], budget := limit, truncated := false }
  if a.truncated then none
  else
    let leaves := a.leaves.reverse.map fun (p, val) =>
      fact pred [.array p, ofValue val]
    let shapes := a.shapes.reverse.flatMap fun (p, kind, n) =>
      [ fact s!"{pred}_kind" [.array p, .str kind],
        fact s!"{pred}_len" [.array p, .integer (Int.ofNat n)] ]
    some (leaves ++ shapes ++ [fact s!"{pred}_truncated" [.bool false]])

/-- Flatten a decoded body into facts, under the names `body`, `body_kind` and
`body_len`, or into `body_truncated(true)` if it has more than `limit` of them or
nests deeper than `maxBodyDepth`.

`pred` is `"body"` for a request and `"response_body"` for a response, so the
two never join by accident. -/
def flatten (pred : String) (v : Value) (limit : Nat) : List Fact :=
  (flatten? pred v limit).getD [fact s!"{pred}_truncated" [.bool true]]

/-- The whole value as one fact, and its flattening; or, for a body past the bounds, only
`…_truncated(true)`. The whole value is built only for a body within them: a term for a map
costs time quadratic in its keys, and a body that is refused anyway is not worth it. -/
private def whole (pred wholePred : String) (v : Value) (limit : Nat) : List Fact :=
  match flatten? pred v limit with
  | some flat => fact wholePred [ofValue v] :: flat
  | none => [fact s!"{pred}_truncated" [.bool true]]

/-- The body facts for a request. -/
def ofBody (v : Value) (limit : Nat) : List Fact := whole "body" "request_body" v limit

/-- The body facts for a response. -/
def ofResponseBody (v : Value) (limit : Nat) : List Fact :=
  whole "response_body" "response_body" v limit

/-- What is emitted when no decoder was configured for the body's media type.

The positive statement matters: a rule can require `body_opaque(false)` and so
refuse to act on a request whose body nobody read, which is exactly the
distinction between "the body says nothing relevant" and "nobody looked". -/
def opaqueBody : List Fact :=
  [fact "body_opaque" [.bool true], fact "body_undecodable" [.bool false],
   fact "body_truncated" [.bool false]]

/-- What is emitted when a decoder *was* configured and could not read the body.

This is a different situation from `opaqueBody` and a much more suspicious one:
the manifest said these bytes are a `git-receive-pack` request and they are
not.  The authorizer refuses on it without the grant having to remember to,
because the alternative is that every `reject if` over body facts is vacuously
satisfied by a body nobody could parse. -/
def undecodableBody : List Fact :=
  [fact "body_opaque" [.bool true], fact "body_undecodable" [.bool true],
   fact "body_truncated" [.bool false]]

/-- The counterpart, emitted whenever a decoder did produce a value. -/
def transparentBody : List Fact :=
  [fact "body_opaque" [.bool false], fact "body_undecodable" [.bool false]]

/-- What is emitted when the request has no body at all. -/
def emptyBody : List Fact :=
  [fact "body_present" [.bool false], fact "body_opaque" [.bool false],
   fact "body_undecodable" [.bool false], fact "body_truncated" [.bool false]]

/-- The counterpart for a request that does have one. -/
def bodyPresent : List Fact := [fact "body_present" [.bool true]]

end Facts
end Kleis
