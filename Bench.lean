import LeanDatalog

/-
A benchmark harness, in Lean rather than in shell.

Programs are not hardcoded here: `benchmark/rules` holds rule sets, each of
which derives nothing on its own, and `benchmark/data` holds fact sets of
increasing size. Every (rules, data) pair is concatenated, parsed once, and
evaluated by each `Evaluator`, so adding a workload means adding a file.

Nothing is asserted about the timings — they belong to the machine, not to
the source. What is recorded is the METHOD. A cell that exceeds the budget
stops that row, so a slow machine simply reports less.
-/

-- Run `act` and report how long it took.
--
-- The result is written into a ref rather than bound with `let`. That is not
-- decoration: `let n := act ()` leaves a thunk, which is not forced until `n`
-- is demanded — after the second clock reading — so every cell times as 0ms
-- while the work still happens. Passing it as an argument forces it, since
-- Lean evaluates arguments at the call.
def timeMs (act: Unit → Nat): IO (Nat × Nat) := do
  let cell ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  cell.set (act ())
  let t1 ← IO.monoMsNow
  return (t1 - t0, ← cell.get)

-- Every `.lp` file in `dir`, by name, so the ordering is the size ordering.
def readPrograms (dir: System.FilePath): IO (List (String × String)) := do
  let entries ← dir.readDir
  let lp := entries.toList.filter λ e ↦ e.path.extension == some "lp"
  let sorted := lp.mergeSort λ a b ↦ a.fileName ≤ b.fileName
  sorted.mapM λ e ↦ do return (e.fileName, ← IO.FS.readFile e.path)

-- One decimal place, without floats.
def ratio (a b: Nat): String :=
  if b == 0 then "  n/a" else s!"{a * 10 / b / 10}.{a * 10 / b % 10}x"

def pad (s: String) (w: Nat): String :=
  s ++ "".pushn ' ' (w - s.length)

def main (args: List String): IO UInt32 := do
  let budget := (args.head?.bind String.toNat?).getD 300
  let rules ← readPrograms "benchmark/rules"
  let data ← readPrograms "benchmark/data"
  if rules.isEmpty || data.isEmpty then
    IO.eprintln "error: benchmark/rules or benchmark/data is empty — run from the repo root"
    return 1
  IO.println s!"budget {budget}ms per cell; a row stops once a cell exceeds it"
  IO.println ""
  for (rname, rsrc) in rules do
    IO.println s!"{rname}"
    IO.println s!"  {pad "data" 10}{pad "atoms" 8}{pad "stepwise" 11}{pad "layerwise" 11}speedup"
    -- Tracked per evaluator, not per row: Stepwise gives out roughly an
    -- order of magnitude sooner, and watching Layerwise carry on past that
    -- point is the interesting part of the table.
    let mut stopS := false
    let mut stopL := false
    for (dname, dsrc) in data do
      if stopS && stopL then
        IO.println s!"  {pad dname 10}(skipped)"
      else
        match parseProgram (rsrc ++ "\n" ++ dsrc) with
        | none => IO.println s!"  {pad dname 10}PARSE ERROR"
        | some p =>
          -- Layerwise first, being the cheap one: if it is already over
          -- budget then Stepwise is hopeless and is not worth starting.
          let mut lTxt := "-"; let mut aTxt := "-"; let mut lms := 0
          if !stopL then
            let (ms, n) ← timeMs λ _ ↦ (Layerwise.saturate p).length
            lms := ms; lTxt := s!"{ms}ms"; aTxt := toString n
            if ms > budget then stopL := true
          let mut sTxt := "-"; let mut sms := 0
          if !stopS && !stopL then
            let (ms, _) ← timeMs λ _ ↦ (Stepwise.saturate p).length
            sms := ms; sTxt := s!"{ms}ms"
            if ms > budget then stopS := true
          else
            stopS := true
          let spd := if sms > 0 && lms > 0 then ratio sms lms else ""
          IO.println s!"  {pad dname 10}{pad aTxt 8}\
{pad sTxt 11}{pad lTxt 11}{spd}"
          (← IO.getStdout).flush
    IO.println ""
  return 0
