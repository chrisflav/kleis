import LeanBiscuit

/-!
# Byte string helpers

The proxy spends its life looking for delimiters in buffers that are still
arriving, so the operations here are the ones a streaming parser needs: find a
needle, split at an index, and decode a prefix as text without failing on a
partial code point.

Everything is total.  A search that finds nothing returns `none`, and a slice
past the end of the buffer is clamped rather than an error, because the caller
is usually asking about bytes that have not been read yet.
-/

namespace Auth
namespace Bytes

open LeanBiscuit (Bytes)

/-- The byte at `i`, or `none` past the end. -/
def get? (b : Bytes) (i : Nat) : Option UInt8 :=
  if h : i < b.size then some b[i] else none

/-- The slice `[start, stop)`, clamped to the buffer. -/
def slice (b : Bytes) (start stop : Nat) : Bytes :=
  let start := min start b.size
  let stop := min stop b.size
  if start ≥ stop then ByteArray.empty else b.extract start stop

/-- The first `n` bytes, or all of them. -/
def take (b : Bytes) (n : Nat) : Bytes := slice b 0 n

/-- Everything after the first `n` bytes. -/
def drop (b : Bytes) (n : Nat) : Bytes := slice b n b.size

/-- Does `b` start with `prefix`? -/
def startsWith (b : Bytes) (pre : Bytes) : Bool :=
  pre.size ≤ b.size && (take b pre.size).toList == pre.toList

/-- The index of the first occurrence of `needle` at or after `from`.

Naive search: the needles here are two to four bytes (`\r\n`, `\r\n\r\n`, a
pkt-line length), so the worst case never arises in practice and a table would
cost more than it saves. -/
def indexOf? (b : Bytes) (needle : Bytes) (from_ : Nat := 0) : Option Nat :=
  if needle.size == 0 then some from_
  else if needle.size > b.size then none
  else
    let last := b.size - needle.size
    let rec go (i : Nat) : Option Nat :=
      if i > last then none
      else if startsWith (drop b i) needle then some i
      else go (i + 1)
    termination_by last + 1 - i
    go from_

/-- The index of the first occurrence of a single byte. -/
def indexOfByte? (b : Bytes) (c : UInt8) (from_ : Nat := 0) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i < b.size then
      if b[i] == c then some i else go (i + 1)
    else none
  termination_by b.size - i
  go from_

/-- Split at the first occurrence of `needle`, dropping it.  `none` when the
needle is absent — which for a streaming parser means "not yet". -/
def splitOnce? (b : Bytes) (needle : Bytes) : Option (Bytes × Bytes) := do
  let i ← indexOf? b needle
  pure (take b i, drop b (i + needle.size))

/-- Decode as UTF-8, replacing anything invalid.  Used for header text and for
diagnostics, never for anything that is forwarded upstream. -/
def toStringLossy (b : Bytes) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => String.ofList (b.toList.map fun c => if c < 128 then Char.ofNat c.toNat else '\uFFFD')

/-- Is this an ASCII carriage return or line feed? -/
def isEol (c : UInt8) : Bool := c == 13 || c == 10

/-- Drop ASCII whitespace from both ends. -/
def trim (b : Bytes) : Bytes :=
  let isWs (c : UInt8) := c == 32 || c == 9 || isEol c
  let rec front (i : Nat) : Nat :=
    if h : i < b.size then (if isWs b[i] then front (i + 1) else i) else i
  termination_by b.size - i
  let rec back (i : Nat) : Nat :=
    match i with
    | 0 => 0
    | j + 1 =>
      match get? b j with
      | some c => if isWs c then back j else i
      | none => i
  termination_by i
  let s := front 0
  let e := back b.size
  if s ≥ e then ByteArray.empty else slice b s e

end Bytes
end Auth
