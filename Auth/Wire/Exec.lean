import Auth.Wire.Registry
import Auth.Util.Json

/-!
# Running a decoder out of process

The escape hatch that makes "a new service costs a file" true even for a wire
format nobody has written Lean for: a command reads the body prefix on its
standard input and writes JSON on its standard output.

It costs a process per request, so it is for the long tail rather than for
anything hot — a format worth serving at volume is worth a decoder in
`Auth.Wire`.  What it buys is that being unable to decode something is never a
reason to be unable to *use* this proxy.

A subprocess that fails, writes nothing, or writes something that is not JSON
yields no value, which the caller turns into `body_undecodable` — and the
authorizer refuses on that. A decoder that cannot be trusted to run is treated
exactly like a decoder that could not read the body.
-/

namespace Auth
namespace Wire

open LeanBiscuit (Bytes)
open LeanBiscuit.Datalog (Value)

/-- How long a decoder subprocess may hold up a request, in bytes of output we
are willing to read.  There is no wall-clock bound: adding one would make the
decision depend on the speed of the machine, which is the one thing the design
keeps out of authorization. -/
def maxExecOutput : Nat := 1048576

/-- Run an out-of-process decoder over an entity prefix. -/
def runExec (command : String) (args : List String) (entity : Bytes) :
    IO (Option Value) := do
  try
    let child ← IO.Process.spawn {
      cmd := command, args := args.toArray
      stdin := .piped, stdout := .piped, stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.write entity
    stdin.flush
    -- Closing standard input is what tells the decoder the body has ended;
    -- without it a decoder that reads to end of file waits forever.
    let out ← child.stdout.readToEnd
    let _ ← child.stderr.readToEnd
    let code ← child.wait
    if code != 0 then return none
    if out.length > maxExecOutput then return none
    match Json.parse out with
    | .ok j => return some j.toValue
    | .error _ => return none
  catch _ => return none

/-- Decode a body with whichever kind of decoder a manifest named.

The pure decoders answer without leaving the process; `exec` shells out; and
`opaque` means nobody was asked to look. -/
def runDecoder (d : Decoder) (entity : Bytes) (complete : Bool) : IO (Option Value) := do
  match d with
  | .pure decoder =>
    match decoder.step entity complete with
    | .done v _ => return some v
    | _ => return none
  | .exec command args => if complete then runExec command args entity else return none
  | .opaque => return none

end Wire
end Auth
