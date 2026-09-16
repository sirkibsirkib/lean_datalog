import LeanDatalog

/-
A benchmark harness, in Lean rather than in shell.

Programs are not hardcoded here: `benchmark/rules` holds rule sets, each of
which derives nothing on its own, and `benchmark/data` holds fact sets of
increasing size. Every (rules, data) pair is concatenated, parsed once, and
evaluated by each `Evaluator`, so adding a workload means adding a file.

Nothing is asserted about the timings — they belong to the machine, not to
the source. What is recorded is the METHOD. Every cell runs to completion,
however long that takes, so a slow machine just waits longer rather than
reporting less.
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

def pad (s: String) (w: Nat): String :=
  s ++ "".pushn ' ' (w - s.length)

def main: IO UInt32 := do
  let rules ← readPrograms "benchmark/rules"
  let data ← readPrograms "benchmark/data"
  if rules.isEmpty || data.isEmpty then
    IO.eprintln "error: benchmark/rules or benchmark/data is empty — run from the repo root"
    return 1
  for (rname, rsrc) in rules do
    IO.println s!"{rname}"
    IO.println s!"  {pad "data" 10}{pad "atoms" 8}{pad "stepwise" 11}{pad "layerwise" 11}matching"
    for (dname, dsrc) in data do
      match parseProgram (rsrc ++ "\n" ++ dsrc) with
      | none => IO.println s!"  {pad dname 10}PARSE ERROR"
      | some p =>
        let (sms, _) ← timeMs λ _ ↦ (Stepwise.saturate p).length
        let (lms, n) ← timeMs λ _ ↦ (Layerwise.saturate p).length
        let (mms, _) ← timeMs λ _ ↦ (Matching.saturate p).length
        IO.println s!"  {pad dname 10}{pad (toString n) 8}\
{pad s!"{sms}ms" 11}{pad s!"{lms}ms" 11}{mms}ms"
        (← IO.getStdout).flush
    IO.println ""
  return 0
