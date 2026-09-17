-- Evaluation. `Interface` fixes what an evaluator is; `Candidates` and
-- `Step` compute consequences by enumeration. Each evaluator is one
-- strategy: `Stepwise` and `Layerwise` enumerate, consuming one atom or a
-- whole round per tick; `Matching` and `SlowMatching` search `kb` instead,
-- and differ only in how their loops terminate.

import LeanDatalog.Eval.Interface
import LeanDatalog.Eval.Candidates
import LeanDatalog.Eval.Step
import LeanDatalog.Eval.Evaluators.Stepwise
import LeanDatalog.Eval.Evaluators.Layerwise
import LeanDatalog.Eval.Evaluators.Matching
import LeanDatalog.Eval.Evaluators.SlowMatching
