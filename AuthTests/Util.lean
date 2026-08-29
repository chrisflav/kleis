import AuthTests.Harness

/-! # Utilities, JSON and TOML -/

namespace AuthTests

open Auth LeanBiscuit

def utilTests : IO Unit := do
  group "util"
  checkEq "percent decode" (Str.percentDecode "a%2Fb%20c") "a/b c"
  checkEq "percent decode keeps a bad escape" (Str.percentDecode "100%") "100%"
  checkEq "plus is a space only in a query" (Str.percentDecode "a+b" true) "a b"
  checkEq "path segments drop empties" (Str.pathSegments "//a//b/").toList ["a", "b"]
  checkEq "query parsing" (Str.parseQuery "/x?a=1&b=&c").toList
    [("a", "1"), ("b", ""), ("c", "")]
  checkEq "strip suffix" (Str.stripSuffix "auth.git" ".git") "auth"
  checkEq "strip suffix leaves a non-match" (Str.stripSuffix "auth" ".git") "auth"
  checkEq "hex round trip" (Str.ofHex? (Str.toHex 48879)) (some 48879)

  group "bytes"
  let b := Bytes.ofString "hello world"
  checkEq "index of" (Auth.Bytes.indexOf? b (Bytes.ofString "wor")) (some 6)
  checkEq "index of absent" (Auth.Bytes.indexOf? b (Bytes.ofString "zzz")) none
  checkEq "trim" (Auth.Bytes.toStringLossy (Auth.Bytes.trim (Bytes.ofString "  x \r\n"))) "x"

  group "base64"
  checkEq "encode" (Auth.Base64.encode (Bytes.ofString "any carnal pleasure.")) "YW55IGNhcm5hbCBwbGVhc3VyZS4="
  checkEq "decode round trip"
    ((Auth.Base64.decode? (Auth.Base64.encode (Bytes.ofString "hi?"))).map Auth.Bytes.toStringLossy)
    (some "hi?")

  group "json"
  match Json.parse "{\"a\": [1, 2, {\"b\": null}], \"c\": true}" with
  | .error e => check "parse an object" false e
  | .ok j =>
    check "parse an object" true
    checkEq "nested lookup" ((j.field? "c").bind Json.asBool?) (some true)
    checkEq "array length" ((j.field? "a").bind Json.asArray? |>.map (·.length)) (some 3)
  checkEq "escapes survive a round trip"
    ((Json.parse (Json.render (.str "a\"b\nc"))).toOption.bind Json.asString?)
    (some "a\"b\nc")
  check "trailing input is refused" (Json.parse "{} x").toOption.isNone
  check "an unterminated object is refused" (Json.parse "{\"a\": 1").toOption.isNone

  group "toml"
  let src := "name = \"github\"\n\
    hosts = [\"a.com\", \"b.com\"]\n\
    datalog = '''\nline one\nline two\n'''\n\
    [credential]\nprovider = \"static\"\n\
    [[route]]\nmatch = \"GET a.com /x\"\n\
    [[route]]\nmatch = \"PUT a.com /y\"\n"
  match Toml.parse src with
  | .error e => check "parse a manifest shape" false e
  | .ok j =>
    check "parse a manifest shape" true
    checkEq "top level string" (j.str? "name") (some "github")
    checkEq "array of strings" ((j.arr? "hosts").filterMap Json.asString?) ["a.com", "b.com"]
    checkEq "multi-line string" (j.str? "datalog") (some "line one\nline two\n")
    checkEq "nested table" (((j.field? "credential").getD (.obj [])).str? "provider")
      (some "static")
    checkEq "array of tables" (j.arr? "route").length 2
    checkEq "second table" (((j.arr? "route")[1]!).str? "match") (some "PUT a.com /y")

end AuthTests
