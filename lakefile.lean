import Lake
open Lake DSL

package kleis where
  version := v!"0.1.0"
  testDriver := "tests"
  moreLinkArgs := #["-lssl", "-lcrypto"]

-- Pinned to a revision rather than tracking a branch: what this builds against
-- is the thing whose datalog engine and curve arithmetic the properties in
-- DESIGN.md are stated over, and a dependency that moved underneath them would
-- make those statements about something else.
require «lean-biscuit» from git
  "https://github.com/chrisflav/lean-biscuit" @ "7fbe9020beebcb1b385ca6d31c8711ffb6361e26"

/-- Compile a C shim under `ffi/` into a static library of the same name. -/
private def ffiStaticLib (pkg : Package) (name : String) : FetchM (Job System.FilePath) := do
  let cFile := pkg.dir / "ffi" / s!"{name}.c"
  let cSrc ← inputTextFile cFile
  let oFile := pkg.buildDir / "ffi" / s!"{name}.o"
  let oJob ← buildFileAfterDep oFile cSrc fun _ => do
    compileO oFile cFile #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  let libFile := pkg.buildDir / "lib" / nameToStaticLib name
  liftM <| buildFileAfterDep libFile oJob fun oFile => do
    compileStaticLib libFile #[oFile]

/-- TLS over OpenSSL, backing `Kleis.Net.Tls`.  A byte transform over memory
BIOs: it never sees a socket. -/
extern_lib Tls pkg := ffiStaticLib pkg "Tls"

/-- Name resolution, backing `Kleis.Net.Resolve`.  Lean's networking has sockets
but no resolver. -/
extern_lib Net pkg := ffiStaticLib pkg "Net"

@[default_target]
lean_lib Kleis

lean_lib KleisTests where
  globs := #[.andSubmodules `KleisTests]

/-- The client: everything a person types. -/
@[default_target]
lean_exe kleis where
  root := `Main

/-- The daemon: the proxy and the control API, in the one process that holds
credentials. -/
@[default_target]
lean_exe kleisd where
  root := `Kleisd

lean_exe tests where
  root := `KleisTests.Main
