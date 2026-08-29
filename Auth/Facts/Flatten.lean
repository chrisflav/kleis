import Auth.Facts.Primitive

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

The whole thing is bounded.  Past `limit` scalars nothing is emitted but
`body_truncated(true)`, and the authorizer's preamble denies on that fact — a
body too large to reason about is a refusal, not a blind spot.
-/

namespace Auth
namespace Facts

open LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

/-- A path into a value: string keys and array indices, outermost first. -/
abbrev Path := List Builder.Term

/-- What flattening accumulates: the leaves and the container descriptions
found so far, in reverse, and how much budget is left. -/
private structure Acc where
  /-- Scalar leaves, reversed. -/
  leaves : List (Path × Value)
  /-- Container descriptions, reversed. -/
  shapes : List (Path × String × Nat)
  /-- Remaining budget, in leaves. -/
  budget : Nat
  /-- Whether the budget ran out. -/
  truncated : Bool

mutual

/-- Walk one node. -/
private def walk (path : Path) (v : Value) (a : Acc) : Acc :=
  if a.budget == 0 then { a with truncated := true } else
  match v with
  | .array l =>
    let a := { a with shapes := (path, "array", l.length) :: a.shapes }
    walkList path 0 l a
  | .set l =>
    let a := { a with shapes := (path, "set", l.length) :: a.shapes }
    walkList path 0 l a
  | .map entries =>
    let a := { a with shapes := (path, "map", entries.length) :: a.shapes }
    walkEntries path entries a
  | scalar =>
    { a with leaves := (path, scalar) :: a.leaves, budget := a.budget - 1 }

/-- Walk the elements of an array or set, indexed by position. -/
private def walkList (path : Path) (i : Nat) : List Value → Acc → Acc
  | [], a => a
  | x :: xs, a =>
    let a := walk (path ++ [.integer (Int.ofNat i)]) x a
    walkList path (i + 1) xs a

/-- Walk the members of a map. -/
private def walkEntries (path : Path) : List (ValueKey × Value) → Acc → Acc
  | [], a => a
  | (k, v) :: xs, a =>
    let key : Builder.Term := match k with
      | .integer i => .integer i
      | .str s => .str s
    let a := walk (path ++ [key]) v a
    walkEntries path xs a

end

/-- Flatten a decoded body into facts, under the names `body`, `body_kind` and
`body_len`, or into `body_truncated(true)` if it is too large.

`pred` is `"body"` for a request and `"response_body"` for a response, so the
two never join by accident. -/
def flatten (pred : String) (v : Value) (limit : Nat) : List Fact :=
  let a := walk [] v { leaves := [], shapes := [], budget := limit, truncated := false }
  if a.truncated then [fact s!"{pred}_truncated" [.bool true]]
  else
    let leaves := a.leaves.reverse.map fun (p, val) =>
      fact pred [.array p, ofValue val]
    let shapes := a.shapes.reverse.flatMap fun (p, kind, n) =>
      [ fact s!"{pred}_kind" [.array p, .str kind],
        fact s!"{pred}_len" [.array p, .integer (Int.ofNat n)] ]
    leaves ++ shapes ++ [fact s!"{pred}_truncated" [.bool false]]

/-- The body facts for a request: the whole value, and its flattening. -/
def ofBody (v : Value) (limit : Nat) : List Fact :=
  fact "request_body" [ofValue v] :: flatten "body" v limit

/-- The body facts for a response. -/
def ofResponseBody (v : Value) (limit : Nat) : List Fact :=
  fact "response_body" [ofValue v] :: flatten "response_body" v limit

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
end Auth
