import Auth.Model.Request

/-!
# Primitive facts

The mechanical part of turning a request into datalog: emitted for every
request, identically, with no manifest involvement.  A manifest that says
nothing at all still gets these, and a policy written against them alone works
against any service.

The vocabulary is deliberately small and deliberately flat.  Everything with
internal structure — a path, a body — is emitted both whole and taken apart, so
that a rule can either match a shape or join on a piece.
-/

namespace Auth
namespace Facts

open LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

/-- A fact with its terms spelled out. -/
abbrev Fact := Builder.Fact

/-- Build a fact from a name and terms. -/
def fact (name : String) (terms : List Builder.Term) : Fact := ⟨⟨name, terms⟩⟩

/-- A string term. -/
def str (s : String) : Builder.Term := .str s

/-- An integer term. -/
def int (n : Nat) : Builder.Term := .integer (Int.ofNat n)

mutual

/-- Translate a decoded value into a builder term. -/
def ofValue : Value → Builder.Term
  | .integer i => .integer i
  | .str s => .str s
  | .date d => .date d
  | .bytes b => .bytes b
  | .bool b => .bool b
  | .null => .null
  | .set l => .set (Builder.mkSet (ofValueList l))
  | .array l => .array (ofValueList l)
  | .map entries => .map (Builder.mkMap (ofValueEntries entries))

/-- Translate a list of values. -/
def ofValueList : List Value → List Builder.Term
  | [] => []
  | x :: xs => ofValue x :: ofValueList xs

/-- Translate a list of map entries. -/
def ofValueEntries : List (ValueKey × Value) → List (Builder.MapKey × Builder.Term)
  | [] => []
  | (k, v) :: xs =>
    let k' : Builder.MapKey := match k with
      | .integer i => .integer i
      | .str s => .str s
    (k', ofValue v) :: ofValueEntries xs

end

/-- The facts every request produces, whatever service it is for. -/
def ofRequest (r : Model.Request) : List Fact :=
  let base : List Fact :=
    [ fact "request_method" [str r.method],
      fact "request_scheme" [str r.scheme],
      fact "request_host" [str r.host],
      fact "request_port" [int r.port],
      fact "request_path" [str r.path],
      fact "request_url" [str r.url],
      fact "request_authority" [str r.authority],
      fact "request_segment_count" [int r.segments.size] ]
  let segments := r.segments.toList.zipIdx.map fun (s, i) =>
    fact "request_segment" [int i, str s]
  let headers := r.headers.toList.map fun (k, v) => fact "request_header" [str k, str v]
  let query := r.query.toList.map fun (k, v) => fact "request_query" [str k, str v]
  let size := match r.bodySize with
    | some n => [fact "request_size" [int n]]
    | none => []
  base ++ segments ++ headers ++ query ++ size

/-- The facts a response produces, for the response-side checks. -/
def ofResponse (r : Model.Response) : List Fact :=
  fact "response_status" [int r.status] ::
    r.headers.toList.map fun (k, v) => fact "response_header" [str k, str v]

/-- The ambient facts: what is true of the moment rather than of the request. -/
def ambient (now : Nat) (clientIp : String) (requestId : String) : List Fact :=
  [ fact "time" [.date now],
    fact "client_ip" [str clientIp],
    fact "request_id" [str requestId] ]

end Facts
end Auth
