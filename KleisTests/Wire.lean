import KleisTests.Harness

/-! # Decoders -/

namespace KleisTests

open Kleis LeanBiscuit
open LeanBiscuit.Datalog (Value ValueKey)

/-- A git pkt-line. -/
private def pkt (payload : String) : String :=
  let len := payload.utf8ByteSize + 4
  let hex := Str.toHex len
  String.ofList (List.replicate (4 - hex.length) '0') ++ hex ++ payload

private def zero : String := String.ofList (List.replicate 40 '0')
private def oidA : String := String.ofList (List.replicate 40 'a')
private def oidB : String := String.ofList (List.replicate 40 'b')

/-- Follow a path into a decoded value, for the assertions below. -/
private def at? : Value → List String → Option Value
  | v, [] => some v
  | .map entries, k :: rest =>
    (entries.find? fun (key, _) => key == ValueKey.str k).bind fun (_, v) => at? v rest
  | .array l, k :: rest => (k.toNat?.bind fun i => l[i]?).bind fun v => at? v rest
  | _, _ => none

private def str? (v : Value) (path : List String) : Option String :=
  match at? v path with
  | some (.str s) => some s
  | _ => none

private def bool? (v : Value) (path : List String) : Option Bool :=
  match at? v path with
  | some (.bool b) => some b
  | _ => none

def wireTests : IO Unit := do
  group "json decoder"
  match Wire.jsonDecoder.step (Bytes.ofString "{\"base\": \"main\"}") true with
  | .done v _ => checkEq "field" (str? v ["base"]) (some "main")
  | _ => check "a complete JSON body decodes" false
  match Wire.jsonDecoder.step (Bytes.ofString "{\"base\":") false with
  | .need _ => check "a partial JSON body asks for more" true
  | _ => check "a partial JSON body asks for more" false
  match Wire.jsonDecoder.step (Bytes.ofString "not json") true with
  | .opaque => check "an unparseable body is opaque, not an error" true
  | _ => check "an unparseable body is opaque, not an error" false

  group "form decoder"
  match Wire.formDecoder.step (Bytes.ofString "a=1&b=x+y&a=2") true with
  | .done v _ => do
    checkEq "single value" (str? v ["b"]) (some "x y")
    -- A repeated name must not lose a value: dropping one would let a request
    -- smuggle a parameter past a policy that checked the other.
    checkEq "repeated name becomes an array" (str? v ["a", "1"]) (some "2")
  | _ => check "a form body decodes" false

  group "git receive-pack"
  let push := pkt s!"{oidA} {oidB} refs/heads/dev/x\x00report-status\n"
    ++ pkt s!"{oidA} {zero} refs/heads/old\n"
    ++ "0000PACK" ++ String.ofList (List.replicate 500 'x')
  match Wire.gitReceivePackDecoder.step (Bytes.ofString push) false with
  | .done v consumed => do
    checkEq "kind" (str? v ["kind"]) (some "receive-pack")
    checkEq "first ref" (str? v ["updates", "0", "ref"]) (some "refs/heads/dev/x")
    checkEq "second ref" (str? v ["updates", "1", "ref"]) (some "refs/heads/old")
    checkEq "a zero new id is a delete" (bool? v ["updates", "1", "delete"]) (some true)
    checkEq "and not a create" (bool? v ["updates", "1", "create"]) (some false)
    checkEq "capabilities" (str? v ["capabilities", "0"]) (some "report-status")
    -- The property the whole design leans on: what the decoder consumes is
    -- fixed by the pkt-lines and does not grow with the packfile behind them.
    let bigger := pkt s!"{oidA} {oidB} refs/heads/dev/x\x00report-status\n"
      ++ pkt s!"{oidA} {zero} refs/heads/old\n"
      ++ "0000PACK" ++ String.ofList (List.replicate 100000 'x')
    match Wire.gitReceivePackDecoder.step (Bytes.ofString bigger) false with
    | .done _ consumed' =>
      check "the prefix read does not grow with the packfile" (consumed == consumed')
        s!"{consumed} vs {consumed'}"
    | _ => check "a large push decodes" false
    check "and is a small prefix" (consumed < 300) s!"consumed {consumed}"
  | _ => check "a push decodes" false

  let create := pkt s!"{zero} {oidB} refs/heads/new\n" ++ "0000PACK"
  match Wire.gitReceivePackDecoder.step (Bytes.ofString create) false with
  | .done v _ => checkEq "a zero old id is a create" (bool? v ["updates", "0", "create"]) (some true)
  | _ => check "a create decodes" false

  group "git upload-pack"
  let fetch := pkt s!"want {oidA} multi_ack\n" ++ pkt s!"want {oidB}\n" ++ "0000"
    ++ pkt s!"have {oidA}\n" ++ pkt "done\n"
  match Wire.gitUploadPackDecoder.step (Bytes.ofString fetch) true with
  | .done v _ => do
    checkEq "kind" (str? v ["kind"]) (some "upload-pack")
    checkEq "first want" (str? v ["wants", "0"]) (some oidA)
    checkEq "second want" (str? v ["wants", "1"]) (some oidB)
  | _ => check "a fetch decodes" false

  let v2 := pkt "command=fetch\n" ++ pkt "object-format=sha1\n" ++ "0001"
    ++ pkt "thin-pack\n" ++ pkt s!"want {oidA}\n" ++ "0000"
  match Wire.gitUploadPackDecoder.step (Bytes.ofString v2) true with
  | .done v _ => do
    checkEq "protocol v2 kind" (str? v ["kind"]) (some "v2")
    checkEq "v2 command" (str? v ["command"]) (some "fetch")
  | _ => check "a v2 request decodes" false

  match Wire.gitReceivePackDecoder.step (Bytes.ofString "not pkt-lines at all") true with
  | .opaque => check "garbage is opaque" true
  | _ => check "garbage is opaque" false

  group "decoder registry"
  checkEq "by media type"
    ((Wire.byMedia? "application/json; charset=utf-8").map (·.name)) (some "json")
  checkEq "by name" ((Wire.byName? "git-receive-pack").map (·.name)) (some "git-receive-pack")
  checkEq "unknown media type" ((Wire.byMedia? "application/octet-stream").map (·.name)) none

end KleisTests
