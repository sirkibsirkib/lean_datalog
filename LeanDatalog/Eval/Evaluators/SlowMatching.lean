import LeanDatalog.Eval.Evaluators.Matching

/-
The same backtracking matcher as Matching.lean (`Matching.stepImage`,
reused unchanged), wired to a saturation loop that filters every candidate
down to the Herbrand base up front and lets Lean's well-founded recursion
track termination directly — the way Stepwise.lean does, and the way this
evaluator's `saturateGo` did before Matching.lean switched to fuel.

The filter genuinely does make "everything produced lands in the base"
hold unconditionally, with no `kb`-bounded hypothesis needed, which is
exactly what `decreasing_by` below needs to typecheck without threading
extra state through `saturateGo`'s own recursive argument list. But
`p.herbrand_base` grows with the square of the constants a program
mentions, and this filter pays a membership check against it for EVERY
candidate on EVERY tick — cost that has nothing to do with how many
candidates actually match, only with how many constants the program
happens to mention. `benchmark/rules/clutter.lp` is built to make that
cost dominate: matching's whole advantage over enumeration is skipping
work that scales with unused constants, and this filter reintroduces
exactly that scaling. Compare this file's benchmark row to `matching`'s.
-/

def Program.slowMatchStepAtoms (p: Program) (kb: List GrAtom): List GrAtom :=
  (Matching.stepImage p kb).filter (λ a ↦ decide (a ∈ p.herbrand_base))

-- No boundedness hypothesis needed: this is `Matching.mem_stepImage_core`,
-- restricted to the atoms that survive the filter.
theorem Program.mem_slowMatchStepAtoms {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.slowMatchStepAtoms kb →
    ∃ r ∈ p, ∃ σ: Subst, (∀ b ∈ r.body, Subst.grounded b σ ∈ kb) ∧ a = Subst.grounded r.head σ
:= λ ha ↦ Matching.mem_stepImage_core (List.mem_filter.mp ha).1

-- Unconditionally in the base, by construction of the filter — no need for
-- `kb` itself to be bounded first, which is the whole point of filtering.
theorem Program.slowMatchStepAtoms_mem_herbrand_base {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.slowMatchStepAtoms kb → a ∈ p.herbrand_base
:= λ ha ↦ of_decide_eq_true (List.mem_filter.mp ha).2

theorem Program.mem_slowMatchStepAtoms_of_fires {p: Program} {r: Rule} {σ: Subst} {kb: List GrAtom}
    (hr: r ∈ p) (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base)
    (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    Subst.grounded r.head σ ∈ p.slowMatchStepAtoms kb
:= List.mem_filter.mpr
    ⟨Matching.mem_stepImage_of_fires hr hbody,
     decide_eq_true (Program.grounded_head_mem_herbrand_base hr (Program.subst_consts hbound hbody))⟩

namespace SlowMatching

-- One tick per derived atom, exactly like Stepwise.lean's loop: the filter
-- above is what lets Lean's own decreasing-measure tracking carry the
-- whole termination proof, with no fuel and no invariant threaded through
-- `kb`.
def saturateGo (p: Program) (kb: List GrAtom): List GrAtom :=
  match _hfind: (p.slowMatchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
  | none => kb
  | some a => saturateGo p (a :: kb)
termination_by p.herbrand_base.countP λ b ↦ decide (b ∉ kb)
decreasing_by
  have hmem := List.mem_of_find?_eq_some _hfind
  have hnew: a ∉ kb := by simpa using List.find?_some _hfind
  refine List.countP_lt_countP (a := a)
    ?_ (Program.slowMatchStepAtoms_mem_herbrand_base hmem) ?_ ?_
  · intro x _ hx
    simp only [decide_eq_true_iff] at hx ⊢
    exact λ hg ↦ hx (.tail _ hg)
  · simpa using hnew
  · simp only [decide_eq_true_iff]
    exact λ h ↦ h (.head _)

def saturate (p: Program): List GrAtom :=
  saturateGo p []

theorem saturateGo_fixpoint (p: Program):
  ∀ kb, ∀ a ∈ p.slowMatchStepAtoms (saturateGo p kb), a ∈ saturateGo p kb
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
    | head _ => exact Program.slowMatchStepAtoms_mem_herbrand_base (List.mem_of_find?_eq_some hfind)
    | tail _ hg => exact hb g hg

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
    refine ih (.snoc _ _ _ h ?_)
    obtain ⟨r, hr, σ, hbody, rfl⟩ :=
      Program.mem_slowMatchStepAtoms (List.mem_of_find?_eq_some hfind)
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
      (Program.mem_slowMatchStepAtoms_of_fires hr hbound hfires))

def evaluator: Evaluator := ⟨saturate, saturate_model⟩

end SlowMatching
