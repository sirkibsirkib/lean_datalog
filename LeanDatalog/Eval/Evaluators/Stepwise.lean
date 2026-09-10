import LeanDatalog.Eval.Step
import LeanDatalog.Eval.Interface

/-
Saturation one atom at a time.

Each tick applies exactly one rule instance, which is exactly one
`Program.infer` step, so the loop is the relation of Semantics.lean
unrolled:

  tick        1         2           3
         ∅ ──────▸ {a} ──────▸ {a,b} ──────▸ {a,b,c} ──▸ ⋯
              +a         +b           +c

That correspondence is what this implementation is for: `saturateGo` and
`Program.infer` advance in lockstep, so reachability is a direct induction
over the loop rather than an argument about batches.

It is not the quick way to compute. `stepAtoms` yields every consequence of
the current knowledge base, and each tick keeps a single one of them and
recomputes the rest next time; Layerwise.lean keeps them all.
-/

namespace Stepwise

-- One tick per atom derived, since each keeps a single element of the round.
-- Writing M for the size of the model and using the cost of `stepAtoms`
-- (see Step.lean for the parameters):
--
--   ticks = M        total  Θ(P·B·A · C^V · M²)
--
-- One factor of M is the ticks; the other is `kb` growing under the
-- membership tests. The provable bound replaces M by |herbrand_base|, which
-- is loose — the base counts every groundable atom, the model only the
-- derivable ones.
def saturateGo (p: Program) (kb: List GrAtom):
    List GrAtom :=
  match _hfind: (p.stepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
  | none => kb
  | some a => saturateGo p (a :: kb)
termination_by p.herbrand_base.countP λ b ↦ decide (b ∉ kb)
decreasing_by
  have hmem := List.mem_of_find?_eq_some _hfind
  have hnew: a ∉ kb := by simpa using List.find?_some _hfind
  refine List.countP_lt_countP (a := a)
    ?_ (Program.stepAtoms_mem_herbrand_base hmem) ?_ ?_
  · -- unknown after implies unknown before: plain weakening
    intro x _ hx
    simp only [decide_eq_true_iff] at hx ⊢
    exact λ hg ↦ hx (.tail _ hg)
  · -- `a` was unknown before
    simpa using hnew
  · -- ...and is known now, since `a` heads the list
    simp only [decide_eq_true_iff]
    exact λ h ↦ h (.head _)

def saturate (p: Program): List GrAtom :=
  saturateGo p []

-- The loop returns only at a fixpoint: `find?` yielding nothing means every
-- consequence of the knowledge base is already in it.
theorem saturateGo_fixpoint (p: Program):
  ∀ kb, ∀ a ∈ p.stepAtoms (saturateGo p kb), a ∈ saturateGo p kb
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hfind =>
    rw [saturateGo.eq_def, hfind]
    intro a ha
    simpa using List.find?_eq_none.mp hfind a ha
  | case2 kb a hfind ih =>
    rw [saturateGo.eq_def, hfind]
    exact ih

-- The Herbrand bound is an invariant of the loop.
theorem saturateGo_bounded (p: Program):
  ∀ kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    ∀ g ∈ saturateGo p kb, g ∈ p.herbrand_base
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hfind =>
    intro hb
    rw [saturateGo.eq_def, hfind]
    exact hb
  | case2 kb a hfind ih =>
    intro hb
    rw [saturateGo.eq_def, hfind]
    refine ih (λ g hg ↦ ?_)
    cases hg with
    | head _ => exact Program.stepAtoms_mem_herbrand_base (List.mem_of_find?_eq_some hfind)
    | tail _ hg => exact hb g hg

-- Each iteration is one `infer` step, so the result stays reachable.
theorem saturateGo_reachable (p: Program):
  ∀ kb, p.infer.ReflTransGen ∅ (λ g ↦ g ∈ kb) →
    p.infer.ReflTransGen ∅ (λ g ↦ g ∈ saturateGo p kb)
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hfind =>
    intro h
    rw [saturateGo.eq_def, hfind]
    exact h
  | case2 kb a hfind ih =>
    intro h
    rw [saturateGo.eq_def, hfind]
    refine ih (.scoc _ _ _ h ?_)
    obtain ⟨r, hr, σ, _, hbody, rfl⟩ :=
      Program.mem_stepAtoms (List.mem_of_find?_eq_some hfind)
    have hnew := List.find?_some hfind
    simp only [decide_eq_true_iff] at hnew
    exact ⟨r, hr, σ, hbody, hnew, Set.ofList_cons⟩

theorem saturate_model (p: Program):
    p.model (· ∈ saturate p)
:= by
  have hbound := saturateGo_bounded p [] (λ g hg ↦ nomatch hg)
  constructor
  · refine saturateGo_reachable p [] ?_
    rw [Set.ofList_nil]
    exact .refl _
  · rintro ⟨kb', r, hr, σ, hfires, hnew, _⟩
    exact hnew (saturateGo_fixpoint p [] _
      (Program.mem_stepAtoms_of_fires hr hbound hfires))

def evaluator: Evaluator := ⟨saturate, saturate_model⟩

end Stepwise
