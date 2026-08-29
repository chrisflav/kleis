import Auth.Util.Bytes

/-!
# Reading a ClientHello

Enough of the TLS record and handshake layer to find the server name a client
asked for, and no more.

This exists so that certificate selection stays in Lean.  OpenSSL can be told
to call back into the application when it sees an SNI, but that means a C
callback re-entering the Lean runtime in the middle of a handshake; peeking at
the first record before any TLS session exists is simpler, keeps the choice of
certificate somewhere a person can read it, and is only the fifty lines below.

The bytes are then handed to the session unchanged, so the peek costs nothing:
it is a read of a buffer the proxy was going to hold anyway.
-/

namespace Auth
namespace Net

open LeanBiscuit (Bytes)

/-- Read a big-endian number of `n` bytes at `off`. -/
private def be (b : Bytes) (off n : Nat) : Option Nat :=
  if off + n > b.size then none
  else some ((List.range n).foldl (fun acc i => acc * 256 + (b[off + i]!).toNat) 0)

/-- Find the SNI in the extension block starting at `off`. -/
private def findSni (b : Bytes) (off stop : Nat) : Nat → Option String
  | 0 => none
  | fuel + 1 => do
    if off + 4 > stop then none else
    let extType ← be b off 2
    let extLen ← be b (off + 2) 2
    let body := off + 4
    if body + extLen > stop then none
    else if extType == 0 then do
      -- server_name: a list of entries, each a type byte, a length and a name.
      let listLen ← be b body 2
      let entry := body + 2
      if listLen < 3 || entry + 3 > stop then none else
        let nameLen ← be b (entry + 1) 2
        if entry + 3 + nameLen > stop then none
        else some (Bytes.toStringLossy (Bytes.slice b (entry + 3) (entry + 3 + nameLen)))
    else findSni b (body + extLen) stop fuel

/-- The server name a ClientHello asked for, if the buffer holds a complete
one.

`none` covers three different situations on purpose — not enough bytes yet, not
a ClientHello, no SNI extension — because the caller does the same thing in all
three: fall back to the address the connection was made to. -/
def clientHelloSni? (buf : Bytes) : Option String := do
  -- TLS record: type 22 (handshake), version, length.
  if buf.size < 6 then none else
  if buf[0]! != 22 then none else
  let recordLen ← be buf 3 2
  let recordEnd := 5 + recordLen
  if buf.size < recordEnd then none else
  -- Handshake: type 1 (client_hello), 24 bit length.
  if buf[5]! != 1 then none else
  let bodyLen ← be buf 6 3
  let body := 9
  let bodyEnd := body + bodyLen
  if bodyEnd > recordEnd then none else
  -- version (2), random (32), then the session id.
  let sessionIdLen ← be buf (body + 34) 1
  let afterSession := body + 35 + sessionIdLen
  let cipherLen ← be buf afterSession 2
  let afterCiphers := afterSession + 2 + cipherLen
  let compLen ← be buf afterCiphers 1
  let afterComp := afterCiphers + 1 + compLen
  if afterComp + 2 > bodyEnd then none else
  let extLen ← be buf afterComp 2
  let extStart := afterComp + 2
  let extStop := min (extStart + extLen) bodyEnd
  findSni buf extStart extStop 64

/-- How many bytes are needed before `clientHelloSni?` can decide.

A ClientHello is one record and a record is at most 16 KiB, so waiting for the
length prefix and then the record is bounded by construction. -/
def clientHelloNeeded (buf : Bytes) : Nat :=
  if buf.size < 5 then 5
  else match be buf 3 2 with
    | some n => 5 + n
    | none => 5

end Net
end Auth
