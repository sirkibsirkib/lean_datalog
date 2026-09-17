import LeanDatalog.SemanticProps

/-
What it means to be an evaluator.

`Program.model` is the specification, already fixed in Semantics.lean, so
this structure is not inventing an abstraction — it names the obligation
every implementation must already meet. Bundling the proof with the
function means an unproved implementation cannot be plugged in.

The result is a `List GrAtom` rather than a `Kb` because a `Kb` is
`Prop`-valued and so carries no runtime data; `eval` below is the bridge
back to the specification's world.
-/

/-
Three facts every evaluator's `model` proof is assembled from, stated once
over list-backed knowledge bases.
-/

theorem Program.reachable_nil (p: Program):
    p.infer.ReflTransGen ∅ (· ∈ ([]: List GrAtom))
:= Set.ofList_nil ▸ .refl _

-- Consing an unknown head that `r` fires onto `kb` is one `infer` step.
theorem Program.infer_cons {p: Program} {kb: List GrAtom} {r: Rule} {σ: Subst}
    (hr: r ∈ p) (hbody: ∀ b ∈ r.body, σ.grounded b ∈ kb) (hnew: σ.grounded r.head ∉ kb):
    p.infer (· ∈ kb) (· ∈ σ.grounded r.head :: kb)
:= ⟨r, hr, σ, hbody, hnew, Set.ofList_cons⟩

-- A list reachable from ∅ that already holds every head its rules can fire
-- is the model: nothing can step out of it.
theorem Program.model_of_closed {p: Program} {kb: List GrAtom}
    (hreach: p.infer.ReflTransGen ∅ (· ∈ kb))
    (hclosed: ∀ r ∈ p, ∀ σ: Subst, (∀ b ∈ r.body, σ.grounded b ∈ kb) → σ.grounded r.head ∈ kb):
    p.model (· ∈ kb)
:= ⟨hreach, λ ⟨_, r, hr, σ, hfires, hnew, _⟩ ↦ hnew (hclosed r hr σ hfires)⟩

structure Evaluator where
  saturate: Program → List GrAtom
  model: ∀ p: Program, p.model (· ∈ saturate p)

def Evaluator.eval (e: Evaluator) (p: Program): { kb: Kb // p.model kb } :=
  ⟨(· ∈ e.saturate p), e.model p⟩

-- Two evaluators cannot disagree. Each computes a model by construction,
-- and `Program.model_unique` says a program has at most one, so the choice
-- of strategy is invisible in the answer — it can only change how long the
-- answer takes to arrive.
theorem Evaluator.agree (e₁ e₂: Evaluator) (p: Program):
    ((· ∈ e₁.saturate p): Kb) = ((· ∈ e₂.saturate p): Kb)
:= p.model_unique (e₁.model p) (e₂.model p)

-- The same stated on the lists, which is how a caller meets it. The lists
-- themselves may differ in order and duplicates; what they contain may not.
theorem Evaluator.mem_agree (e₁ e₂: Evaluator) (p: Program) (a: GrAtom):
    a ∈ e₁.saturate p ↔ a ∈ e₂.saturate p
:= iff_of_eq (congrFun (e₁.agree e₂ p) a)
