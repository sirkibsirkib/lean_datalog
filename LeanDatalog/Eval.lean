-- Evaluation. `Interface` fixes what an evaluator is; `Candidates` and
-- `Step` are the machinery any enumeration-based strategy shares; each
-- remaining module is one strategy, and they differ only in how much of a
-- round they consume per tick.

import LeanDatalog.Eval.Interface
import LeanDatalog.Eval.Candidates
import LeanDatalog.Eval.Step
import LeanDatalog.Eval.Evaluators.Stepwise
import LeanDatalog.Eval.Evaluators.Layerwise
import LeanDatalog.Eval.Evaluators.Matching
