import Auth

/-!
# A small test harness

Counting rather than asserting: a failure prints what it expected and what it
got and the run continues, so one broken thing does not hide the state of
everything after it.
-/

namespace AuthTests

/-- What a run has seen so far. -/
structure Counts where
  /-- Checks that passed. -/
  passed : Nat := 0
  /-- Checks that failed. -/
  failed : Nat := 0
  deriving Inhabited

/-- The shared tally. -/
initialize counts : IO.Ref Counts ← IO.mkRef {}

/-- Print, flushed, so that output order survives a crash. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Record a check. -/
def check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    counts.modify fun c => { c with passed := c.passed + 1 }
  else
    counts.modify fun c => { c with failed := c.failed + 1 }
    say s!"  FAIL {name}"
    if !detail.isEmpty then say s!"       {detail}"

/-- Check that two values agree. -/
def checkEq [BEq α] [ToString α] (name : String) (got expected : α) : IO Unit :=
  check name (got == expected) s!"got `{got}`, expected `{expected}`"

/-- Announce a group. -/
def group (name : String) : IO Unit := say s!"{name}"

/-- Report, and give the exit status. -/
def report : IO UInt32 := do
  let c ← counts.get
  say ""
  if c.failed == 0 then
    say s!"{c.passed} checks passed"
    return 0
  else
    say s!"{c.passed} passed, {c.failed} FAILED"
    return 1

end AuthTests
