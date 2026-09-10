import LeanDatalog.Parse
import LeanDatalog.Eval

/-
Program entrypoints, kept here rather than in `Main` so that `Main` only
has to choose between them.

`runBatch` reads a whole program at once. `runInteractive` reads a line at
a time, growing the program and reprinting the model after each, so a
session shows how the model develops as rules arrive.
-/

-- `readToEnd` already loops until EOF, so one call drains all of stdin.
def readStdin: IO String := do
  let stdin ← IO.getStdin
  stdin.readToEnd

-- Which evaluation strategy the binary uses. Since every `Evaluator` carries
-- a proof that it computes `Program.model`, and `Program.model_unique` says
-- a program has at most one model, swapping this line cannot change the
-- answer — only how long it takes to get.
def evaluator: Evaluator := Layerwise.evaluator

-- Sorted, so the output is stable rather than in derivation order.
def Program.report (p: Program): List String :=
  ((evaluator.saturate p).map λ a ↦ toString a.val ++ ".").mergeSort (· ≤ ·)

-- Exits 0 once the whole input parses, 1 if it doesn't.
def runBatch: IO UInt32 := do
  let input ← readStdin
  match parseProgram input with
  | none =>
    -- `parseProgram` is all-or-nothing and reports no position, so there is
    -- nothing more specific to say about the failure yet.
    IO.eprintln "error: stdin is not a well-formed Datalog program"
    return 1
  | some p =>
    for line in p.report do
      IO.println line
    return 0

/-
Incremental mode.

Each line is itself a small program, so `parseProgram` reads however many
rules it holds — none, one, or several. A line that fails to parse is
reported and dropped, leaving the program as it was, which is what lets a
session survive a typo.

`partial` because the loop ends only when stdin does, and there is no
measure on an unbounded stream to recurse on. That is a different situation
from the parser's, where a `Nat` bounds the work in advance.
-/
partial def runInteractive: IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop (p: Program): IO UInt32 := do
    let line ← stdin.getLine
    if line.isEmpty then
      return 0                             -- end of input
    else
      let p ←
        match parseProgram line with
        | none => do
          IO.eprintln "error: not a well-formed Datalog line — ignored"
          pure p
        | some newRules => pure (p ++ newRules)
      -- Reprinting the whole model each time, rather than only what is new:
      -- the model is what the program means, and a rule can make earlier
      -- rules derive more. Note this re-evaluates from scratch every line.
      for out in p.report do
        IO.println out
      stdout.flush
      loop p
  loop []
