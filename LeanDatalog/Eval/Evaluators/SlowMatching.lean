import LeanDatalog.Eval.Evaluators.Matching

/-
Matching.lean's walk, saturated the way Stepwise.lean saturates: well-founded
recursion on the count of unknown Herbrand-base atoms. Kept as a cautionary
comparison.

To make that recursion typecheck, every candidate is filtered to the
Herbrand base, so "everything produced is in the base" holds without
knowing `kb` is. The filter costs a linear scan of `p.herbrand_base` per
candidate per tick, and the base grows with the square of the program's
constants — whether or not any fact uses them. That is exactly the cost
matching exists to avoid; compare the two on `benchmark/rules/clutter.lp`.
-/

def Program.slowMatchStepAtoms (p: Program) (kb: List GrAtom): List GrAtom :=
  (p.matchStepAtoms kb).filter (λ a ↦ decide (a ∈ p.herbrand_base))

theorem Program.slowMatchStepAtoms_mem_herbrand_base {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.slowMatchStepAtoms kb → a ∈ p.herbrand_base
:= λ ha ↦ of_decide_eq_true (List.mem_filter.mp ha).2

theorem Program.mem_slowMatchStepAtoms_of_fires {p: Program} {r: Rule} {σ: Subst} {kb: List GrAtom}
    (hr: r ∈ p) (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base)
    (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    Subst.grounded r.head σ ∈ p.slowMatchStepAtoms kb
:= List.mem_filter.mpr ⟨Program.mem_matchStepAtoms_of_fires hr hbody,
    decide_eq_true (Rule.fires_head_mem_herbrand_base (kb := (· ∈ kb)) hr hbound hbody)⟩

namespace SlowMatching

def saturateGo (p: Program) (kb: List GrAtom): List GrAtom :=
  match _hfind: (p.slowMatchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
  | none => kb
  | some a => saturateGo p (a :: kb)
termination_by p.herbrand_base.countP λ b ↦ decide (b ∉ kb)
decreasing_by
  exact List.countP_not_mem_lt (λ _ h ↦ .tail _ h)
    (Program.slowMatchStepAtoms_mem_herbrand_base (List.mem_of_find?_eq_some _hfind))
    (by simpa using List.find?_some _hfind) (.head _)

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
    exact ih (List.forall_mem_cons.mpr
      ⟨Program.slowMatchStepAtoms_mem_herbrand_base (List.mem_of_find?_eq_some hfind), hb⟩)

theorem saturateGo_reachable (p: Program):
  ∀ kb, p.infer.ReflTransGen ∅ (· ∈ kb) →
    p.infer.ReflTransGen ∅ (· ∈ saturateGo p kb)
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
    have hnew: a ∉ kb := by simpa using List.find?_some hfind
    obtain ⟨r, hr, σ, hbody, rfl⟩ :=
      Program.mem_matchStepAtoms (List.mem_filter.mp (List.mem_of_find?_eq_some hfind)).1
    exact ih (.snoc _ _ _ h (Program.infer_cons hr hbody hnew))

theorem saturate_model (p: Program):
    p.model (· ∈ saturate p)
:= Program.model_of_closed (saturateGo_reachable p [] p.reachable_nil)
    λ _ hr _ hf ↦ saturateGo_fixpoint p [] _ (Program.mem_slowMatchStepAtoms_of_fires hr
      (saturateGo_bounded p [] (λ _ h ↦ nomatch h)) hf)

def evaluator: Evaluator := ⟨saturate, saturate_model⟩

end SlowMatching
