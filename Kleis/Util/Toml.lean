import Kleis.Util.Json

/-!
# TOML

A reader for the subset of TOML that configuration here is written in: tables,
arrays of tables, dotted keys, the four string forms, integers, booleans,
arrays and inline tables.  Dates and floats are kept as their source text,
which is all anything downstream does with them.

TOML rather than JSON because a manifest embeds datalog, and datalog is
several lines of source with quotes in it.  In JSON that is one string with
every newline and quote escaped, which nobody can read and everybody gets
wrong; in TOML it is a `"""` block that looks like the datalog it is.

The result is a `Json` value, so that a manifest, a grant and the daemon's API
are all read through the same accessors.
-/

namespace Kleis
namespace Toml

/-- The parser state. -/
private structure P where
  /-- The source, as characters. -/
  src : Array Char
  /-- The current offset. -/
  pos : Nat

private def peek? (p : P) (ahead : Nat := 0) : Option Char :=
  if h : p.pos + ahead < p.src.size then some p.src[p.pos + ahead] else none

private def adv (p : P) (n : Nat := 1) : P := { p with pos := p.pos + n }

private def atEnd (p : P) : Bool := p.pos ≥ p.src.size

private def isInline (c : Char) : Bool := c == ' ' || c == '\t'

/-- Skip spaces and tabs. -/
private def skipInline (p : P) : P :=
  let rec go (p : P) (fuel : Nat) : P :=
    match fuel with
    | 0 => p
    | fuel + 1 => match peek? p with
      | some c => if isInline c then go (adv p) fuel else p
      | none => p
  go p p.src.size

/-- Skip a comment, if one starts here. -/
private def skipComment (p : P) : P :=
  match peek? p with
  | some '#' =>
    let rec go (p : P) (fuel : Nat) : P :=
      match fuel with
      | 0 => p
      | fuel + 1 => match peek? p with
        | some '\n' => p
        | some _ => go (adv p) fuel
        | none => p
    go p p.src.size
  | _ => p

/-- Skip whitespace, newlines and comments: everything between items. -/
private def skipAll (p : P) : P :=
  let rec go (p : P) (fuel : Nat) : P :=
    match fuel with
    | 0 => p
    | fuel + 1 =>
      let p' := skipComment (skipInline p)
      match peek? p' with
      | some '\n' => go (adv p') fuel
      | some '\r' => go (adv p') fuel
      | _ => if p'.pos == p.pos then p' else go p' fuel
  go p p.src.size

/-- Is this a character a bare key may contain? -/
private def isBareKey (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') ||
    c == '_' || c == '-'

/-- Read a basic or literal string body, the opening quote consumed. -/
private def stringBody (p : P) (quote : Char) (escapes : Bool) :
    Except String (String × P) :=
  let rec go (p : P) (acc : List Char) (fuel : Nat) : Except String (String × P) :=
    match fuel with
    | 0 => throw "unterminated string"
    | fuel + 1 =>
      match peek? p with
      | none => throw "unterminated string"
      | some '\n' => throw "a single-line string may not contain a newline"
      | some c =>
        if c == quote then .ok (String.ofList acc.reverse, adv p)
        else if escapes && c == '\\' then
          match peek? p 1 with
          | none => throw "unterminated escape"
          | some e =>
            let p2 := adv p 2
            match e with
            | 'n' => go p2 ('\n' :: acc) fuel
            | 't' => go p2 ('\t' :: acc) fuel
            | 'r' => go p2 ('\r' :: acc) fuel
            | '"' => go p2 ('"' :: acc) fuel
            | '\\' => go p2 ('\\' :: acc) fuel
            | 'b' => go p2 (Char.ofNat 8 :: acc) fuel
            | 'f' => go p2 (Char.ofNat 12 :: acc) fuel
            | 'u' =>
              let ds := (List.range 4).map fun i => peek? p2 i
              match ds.mapM id with
              | none => throw "truncated \\u escape"
              | some cs => match Str.ofHex? (String.ofList cs) with
                | none => throw "malformed \\u escape"
                | some n => go (adv p2 4) (Char.ofNat n :: acc) fuel
            | 'U' =>
              let ds := (List.range 8).map fun i => peek? p2 i
              match ds.mapM id with
              | none => throw "truncated \\U escape"
              | some cs => match Str.ofHex? (String.ofList cs) with
                | none => throw "malformed \\U escape"
                | some n => go (adv p2 8) (Char.ofNat n :: acc) fuel
            | c => throw s!"unknown escape `\\{c}`"
        else go (adv p) (c :: acc) fuel
  go p [] (p.src.size + 1)

/-- Read a multi-line string body, the opening triple quote consumed. -/
private def multilineBody (p : P) (quote : Char) (escapes : Bool) :
    Except String (String × P) :=
  -- A newline immediately after the opening delimiter is not part of the value.
  let p := match peek? p with
    | some '\r' => match peek? p 1 with | some '\n' => adv p 2 | _ => adv p
    | some '\n' => adv p
    | _ => p
  let rec go (p : P) (acc : List Char) (fuel : Nat) : Except String (String × P) :=
    match fuel with
    | 0 => throw "unterminated multi-line string"
    | fuel + 1 =>
      match peek? p with
      | none => throw "unterminated multi-line string"
      | some c =>
        if c == quote && peek? p 1 == some quote && peek? p 2 == some quote then
          .ok (String.ofList acc.reverse, adv p 3)
        else if escapes && c == '\\' then
          match peek? p 1 with
          | some '\n' =>
            -- A backslash at end of line swallows the following whitespace.
            let rec skipWs (p : P) (fuel : Nat) : P :=
              match fuel with
              | 0 => p
              | fuel + 1 => match peek? p with
                | some c => if isInline c || c == '\n' || c == '\r' then skipWs (adv p) fuel else p
                | none => p
            go (skipWs (adv p 1) p.src.size) acc fuel
          | some 'n' => go (adv p 2) ('\n' :: acc) fuel
          | some 't' => go (adv p 2) ('\t' :: acc) fuel
          | some 'r' => go (adv p 2) ('\r' :: acc) fuel
          | some '"' => go (adv p 2) ('"' :: acc) fuel
          | some '\\' => go (adv p 2) ('\\' :: acc) fuel
          | _ => go (adv p) (c :: acc) fuel
        else go (adv p) (c :: acc) fuel
  go p [] (p.src.size + 1)

/-- Read one key: bare, or quoted. -/
private def key (p : P) : Except String (String × P) :=
  match peek? p with
  | some '"' => stringBody (adv p) '"' true
  | some '\'' => stringBody (adv p) '\'' false
  | _ =>
    let rec go (i : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => i
      | fuel + 1 =>
        if h : i < p.src.size then (if isBareKey p.src[i] then go (i + 1) fuel else i) else i
    let stop := go p.pos p.src.size
    if stop == p.pos then throw s!"expected a key at offset {p.pos}"
    else .ok (String.ofList (p.src.extract p.pos stop).toList, { p with pos := stop })

/-- Read a dotted key path. -/
private def keyPath (p : P) : Except String (List String × P) :=
  let rec go (p : P) (acc : List String) (fuel : Nat) : Except String (List String × P) := do
    match fuel with
    | 0 => throw "key path too long"
    | fuel + 1 =>
      let (k, p) ← key (skipInline p)
      let p := skipInline p
      match peek? p with
      | some '.' => go (adv p) (k :: acc) fuel
      | _ => pure ((k :: acc).reverse, p)
  go p [] (p.src.size + 1)

/-- Read a bare value: a number, a boolean or a date, whichever it turns out to
be.  All three keep their source text; only integers are given a distinct
shape, because only integers have datalog counterparts. -/
private def bareValue (p : P) : Except String (Json × P) :=
  let stops (c : Char) := c == ',' || c == ']' || c == '}' || c == '\n' || c == '\r' || c == '#'
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel + 1 =>
      if h : i < p.src.size then (if stops p.src[i] then i else go (i + 1) fuel) else i
  let stop := go p.pos p.src.size
  let raw := Str.trim (String.ofList (p.src.extract p.pos stop).toList)
  let p := { p with pos := stop }
  if raw == "true" then .ok (.bool true, p)
  else if raw == "false" then .ok (.bool false, p)
  else if raw.isEmpty then throw s!"expected a value at offset {p.pos}"
  else
    let cleaned := String.ofList (raw.toList.filter (· != '_'))
    match cleaned.toInt? with
    | some _ => .ok (.num cleaned, p)
    | none =>
      -- A float keeps its text; a date keeps its text.  Neither is a datalog
      -- integer and neither is silently rounded into one.
      if raw.any (fun c => c == '-' || c == ':') then .ok (.str raw, p)
      else .ok (.num cleaned, p)

mutual

/-- Read any value. -/
private def value (p : P) (fuel : Nat) : Except String (Json × P) := do
  match fuel with
  | 0 => throw "value nested too deeply"
  | fuel + 1 =>
    let p := skipInline p
    match peek? p with
    | none => throw "the input ended where a value was expected"
    | some '"' =>
      if peek? p 1 == some '"' && peek? p 2 == some '"' then do
        let (s, p) ← multilineBody (adv p 3) '"' true
        pure (.str s, p)
      else do
        let (s, p) ← stringBody (adv p) '"' true
        pure (.str s, p)
    | some '\'' =>
      if peek? p 1 == some '\'' && peek? p 2 == some '\'' then do
        let (s, p) ← multilineBody (adv p 3) '\'' false
        pure (.str s, p)
      else do
        let (s, p) ← stringBody (adv p) '\'' false
        pure (.str s, p)
    | some '[' => arrayValue (adv p) fuel []
    | some '{' => inlineTable (adv p) fuel []
    | some _ => bareValue p

/-- Read the rest of an array. -/
private def arrayValue (p : P) (fuel : Nat) (acc : List Json) : Except String (Json × P) := do
  match fuel with
  | 0 => throw "value nested too deeply"
  | fuel + 1 =>
    let p := skipAll p
    match peek? p with
    | some ']' => pure (.arr acc.reverse, adv p)
    | none => throw "unterminated array"
    | _ => do
      let (v, p) ← value p fuel
      let p := skipAll p
      match peek? p with
      | some ',' => arrayValue (adv p) fuel (v :: acc)
      | some ']' => pure (.arr (v :: acc).reverse, adv p)
      | _ => throw s!"expected `,` or `]` at offset {p.pos}"

/-- Read the rest of an inline table. -/
private def inlineTable (p : P) (fuel : Nat) (acc : List (String × Json)) :
    Except String (Json × P) := do
  match fuel with
  | 0 => throw "value nested too deeply"
  | fuel + 1 =>
    let p := skipInline p
    match peek? p with
    | some '}' => pure (.obj acc.reverse, adv p)
    | none => throw "unterminated inline table"
    | _ => do
      let (ks, p) ← keyPath p
      let p := skipInline p
      let p ← match peek? p with
        | some '=' => pure (adv p)
        | _ => throw s!"expected `=` at offset {p.pos}"
      let (v, p) ← value p fuel
      let entry := (ks.getLastD "", ks.dropLast.foldr (init := v) fun k acc => .obj [(k, acc)])
      let p := skipInline p
      match peek? p with
      | some ',' => inlineTable (adv p) fuel (entry :: acc)
      | some '}' => pure (.obj (entry :: acc).reverse, adv p)
      | _ => throw s!"expected `,` or `}}` at offset {p.pos}"

end

/-! ## Assembling the document

TOML is written as a sequence of edits to a tree, so reading one means applying
them in order.  Navigating a path descends into the *last* element of an array
of tables, which is what makes a `[[route]]` header extend the array rather
than replace it. -/

/-- Set `key` to `v` at `path`, creating tables on the way and descending into
the last element of any array of tables. -/
private def setIn : Json → List String → String → Json → Except String Json
  | .obj fields, [], k, v =>
    .ok (.obj (if fields.any (fun (k', _) => k' == k)
      then fields.map (fun (k', v') => if k' == k then (k', v) else (k', v'))
      else fields ++ [(k, v)]))
  | .obj fields, step :: rest, k, v =>
    match fields.find? (fun (k', _) => k' == step) with
    | some (_, .obj sub) => do
      let sub ← setIn (.obj sub) rest k v
      .ok (.obj (fields.map fun (k', v') => if k' == step then (k', sub) else (k', v')))
    | some (_, .arr elems) => do
      match elems.getLast? with
      | none => throw s!"`{step}` is an empty array of tables"
      | some last => do
        let last ← setIn last rest k v
        let elems := elems.dropLast ++ [last]
        .ok (.obj (fields.map fun (k', v') => if k' == step then (k', .arr elems) else (k', v')))
    | some _ => throw s!"`{step}` is a value, not a table"
    | none => do
      let sub ← setIn (.obj []) rest k v
      .ok (.obj (fields ++ [(step, sub)]))
  | _, _, _, _ => throw "expected a table"

/-- Append an empty table to the array at `path ++ [k]`. -/
private def pushIn : Json → List String → String → Except String Json
  | .obj fields, [], k =>
    match fields.find? (fun (k', _) => k' == k) with
    | some (_, .arr elems) =>
      .ok (.obj (fields.map fun (k', v') =>
        if k' == k then (k', .arr (elems ++ [.obj []])) else (k', v')))
    | some _ => throw s!"`{k}` is not an array of tables"
    | none => .ok (.obj (fields ++ [(k, .arr [.obj []])]))
  | .obj fields, step :: rest, k =>
    match fields.find? (fun (k', _) => k' == step) with
    | some (_, .obj sub) => do
      let sub ← pushIn (.obj sub) rest k
      .ok (.obj (fields.map fun (k', v') => if k' == step then (k', sub) else (k', v')))
    | some (_, .arr elems) => do
      match elems.getLast? with
      | none => throw s!"`{step}` is an empty array of tables"
      | some last => do
        let last ← pushIn last rest k
        let elems := elems.dropLast ++ [last]
        .ok (.obj (fields.map fun (k', v') => if k' == step then (k', .arr elems) else (k', v')))
    | some _ => throw s!"`{step}` is a value, not a table"
    | none => do
      let sub ← pushIn (.obj []) rest k
      .ok (.obj (fields ++ [(step, sub)]))
  | _, _, _ => throw "expected a table"

/-- Ensure a table exists at `path`, so that an empty `[table]` header still
produces one. -/
private def ensureIn (root : Json) (path : List String) : Except String Json :=
  match path.getLast? with
  | none => .ok root
  | some k =>
    let parent := path.dropLast
    match root with
    | .obj _ => do
      -- `setIn` would overwrite; only create when nothing is there.
      let existing := path.foldl (init := some root) fun acc step =>
        acc.bind fun j => match j with
          | .obj fs => (fs.find? fun (k', _) => k' == step).map (·.2)
          | .arr elems => elems.getLast?
          | _ => none
      match existing with
      | some _ => .ok root
      | none => setIn root parent k (.obj [])
    | _ => throw "expected a table"

/-- Read a whole document. -/
def parse (source : String) : Except String Json :=
  let src := source.toList.toArray
  let rec go (p : P) (root : Json) (path : List String) (fuel : Nat) :
      Except String Json := do
    match fuel with
    | 0 => throw "document too long"
    | fuel + 1 =>
      let p := skipAll p
      if atEnd p then pure root
      else match peek? p with
        | some '[' =>
          if peek? p 1 == some '[' then do
            let (ks, p) ← keyPath (adv p 2)
            let p := skipInline p
            if peek? p != some ']' || peek? p 1 != some ']' then
              throw s!"expected `]]` at offset {p.pos}"
            let root ← pushIn root ks.dropLast (ks.getLastD "")
            go (adv p 2) root ks fuel
          else do
            let (ks, p) ← keyPath (adv p)
            let p := skipInline p
            if peek? p != some ']' then throw s!"expected `]` at offset {p.pos}"
            let root ← ensureIn root ks
            go (adv p) root ks fuel
        | _ => do
          let (ks, p) ← keyPath p
          let p := skipInline p
          let p ← match peek? p with
            | some '=' => pure (adv p)
            | _ => throw s!"expected `=` at offset {p.pos}"
          let (v, p) ← value p (src.size + 1)
          let root ← setIn root (path ++ ks.dropLast) (ks.getLastD "") v
          go p root path fuel
  go ⟨src, 0⟩ (.obj []) [] (src.size + 1)

end Toml
end Kleis
