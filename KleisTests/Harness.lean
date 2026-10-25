import Kleis

/-!
# A small test harness

Counting rather than asserting: a failure prints what it expected and what it
got and the run continues, so one broken thing does not hide the state of
everything after it.
-/

namespace KleisTests

/-- What a run has seen so far. -/
structure Counts where
  /-- Checks that passed. -/
  passed : Nat := 0
  /-- Checks that failed. -/
  failed : Nat := 0
  /-- The names of the checks that failed, in order, for the summary. -/
  failures : Array String := #[]
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
    counts.modify fun c => { c with failed := c.failed + 1, failures := c.failures.push name }
    say s!"  FAIL {name}"
    if !detail.isEmpty then say s!"       {detail}"

/-- Check that two values agree. -/
def checkEq [BEq α] [ToString α] (name : String) (got expected : α) : IO Unit :=
  check name (got == expected) s!"got `{got}`, expected `{expected}`"

/-- Announce a group. -/
def group (name : String) : IO Unit := say s!"{name}"

/-! ## Timing

A timing check asserts that something is not superlinear, which a bound loose
enough for a loaded machine still catches: the regressions these guard against
cost tens to hundreds of times the bound, not twice it.  What a loaded machine
does is slow everything for a while, so a case over its bound is run once more,
against the bound scaled by how much slower the machine is now than it was at the
start of the run, measured on a fixed workload that has nothing to do with the
code under test.  Both times, and the factor, are in the failure. -/

/-- A fixed, linear workload, which allocates the way the code under test does — a
million small strings in a list — as well as computing: a machine short of memory
or of cache is slow at that, and a pass over a byte array alone would not notice.
Its time is the machine's speed. -/
def calibrationWork : IO Nat := do
  -- The size is read at run time, so that the compiler cannot do the work instead.
  let n := 1000000 + (← IO.monoNanosNow) % 2
  let t0 ← IO.monoMsNow
  let total ← IO.lazyPure fun _ =>
    let strings := (List.range n).map fun i => toString i
    strings.foldl (fun acc s => acc + s.length) 0
  -- Used, so that the work is done.
  if total == 0 then say "calibration: nothing summed"
  return (← IO.monoMsNow) - t0

/-- The calibration time at the start of the run: the fastest of three. -/
initialize baseline : IO.Ref (Option Nat) ← IO.mkRef none

/-- The calibration time at the start of the run. -/
def baselineMs : IO Nat := do
  match ← baseline.get with
  | some b => return b
  | none =>
    let mut best := 1000000
    for _ in [0:3] do
      best := min best (← calibrationWork)
    let b := max best 1
    baseline.set (some b)
    return b

/-- How many times slower the machine is now than at the start of the run, between
one and eight. -/
def loadFactor : IO Nat := do
  let base ← baselineMs
  let now ← calibrationWork
  return max 1 (min 8 ((now + base - 1) / base))

/-- Run `attempt` (which answers whether its case was right) and time it.  Within
`boundMs` it passes; otherwise it is run once more, against `boundMs` times the
load factor, and both times are reported. -/
def checkTimed (name : String) (boundMs : Nat) (attempt : IO Bool) : IO Unit := do
  let _ ← baselineMs
  let t0 ← IO.monoMsNow
  let ok ← attempt
  let ms := (← IO.monoMsNow) - t0
  if ok && ms < boundMs then
    check name true
  else if !ok then
    check s!"{name}: wrong answer, in {ms} ms" false
  else
    let factor ← loadFactor
    let t1 ← IO.monoMsNow
    let ok2 ← attempt
    let ms2 := (← IO.monoMsNow) - t1
    check s!"{name}: {ms} ms, then {ms2} ms, against {boundMs} ms × load {factor}"
      (ok2 && ms2 < boundMs * factor)

/-- Report, and give the exit status. -/
def report : IO UInt32 := do
  let c ← counts.get
  say ""
  if c.failed == 0 then
    say s!"{c.passed} checks passed"
    return 0
  else
    say s!"{c.passed} passed, {c.failed} FAILED:"
    for f in c.failures do say s!"  {f}"
    return 1

end KleisTests
