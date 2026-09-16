import LeanDatalog.Eval.Candidates

/-
The immediate-consequence operator: every head derivable from `kb` in a
single step, with its soundness and completeness.

This is shared by every evaluation strategy built on enumeration. A
strategy differs only in how much of `stepAtoms`' output it consumes per
tick — one atom, or all of them — not in how the output is computed.
-/

-- Every consequence of `kb` in one step.
--
-- Cost, writing
--   P = rules in the program        B = longest rule body
--   C = distinct constants          A = largest arity
--   V = most variables in a body    K = |kb|
--
--   Θ(P · C^V · B · A · (V + K))    and with K dominating, Θ(P·B·A · C^V · K)
--
-- Two factors are worth separating. `C^V` is the enumeration: every
-- assignment of constants to a rule's variables is built and tested, so it
-- is paid in full even when `kb` holds nothing a rule could match, and even
-- for constants no fact mentions. `K` is the membership test, a linear scan
-- of an unordered list. Neither depends on how much the round derives.
--
-- Note also that `p.consts.eraseDups` and `r.vars` are recomputed on every
-- call although both are loop-invariant, costing a further Θ((P·B·A)²) per
-- call. Lower order, but avoidable by hoisting them.
def Program.stepAtoms (p: Program) (kb: List GrAtom): List GrAtom :=
  p.flatMap λ r ↦
    (r.candidateSubsts p.consts.eraseDups).filterMap λ σ ↦
      if r.body.all (λ a ↦ decide (σ.grounded a ∈ kb))
      then some (σ.grounded r.head)
      else none

-- The program `p(a).  q(X) :- p(X).`, for the examples below.
private def X: Variable := ⟨"X", by decide⟩
private def a: Constant := ⟨"a", by decide⟩
private def p: Constant := ⟨"p", by decide⟩
private def q: Constant := ⟨"q", by decide⟩
private def prog: Program :=
  [ ⟨⟨p, [.inr a]⟩, []             , by decide⟩
  , ⟨⟨q, [.inl X]⟩, [⟨p, [.inl X]⟩], by decide⟩ ]
private def pa: GrAtom := ⟨⟨p, [.inr a]⟩, by decide⟩
private def qa: GrAtom := ⟨⟨q, [.inr a]⟩, by decide⟩

example: prog.stepAtoms []   = [pa]     := by decide
example: prog.stepAtoms [pa] = [pa, qa] := by decide

-- Everything `stepAtoms` produces is some rule's head under a candidate
-- substitution all of whose body atoms are already known.
theorem Program.mem_stepAtoms {p: Program} {kb: List GrAtom}
    {a: GrAtom}:
    a ∈ p.stepAtoms kb →
    ∃ r ∈ p, ∃ σ: Subst,
      (∀ v ∈ r.vars, σ v ∈ p.consts)
    ∧ (∀ b ∈ r.body, Subst.grounded b σ ∈ kb)
    ∧ a = Subst.grounded r.head σ
:= by
  intro ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨σ, hσ, heq⟩ := List.mem_filterMap.mp ha
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hσ
  by_cases hcond: r.body.all (λ b ↦ decide (Subst.grounded b (Subst.ofAssoc l) ∈ kb))
  · rw [if_pos hcond] at heq
    refine ⟨r, hr, _, ?_, ?_, (Option.some.inj heq).symm⟩
    · exact λ v hv ↦ List.mem_eraseDups.mp (Subst.ofAssoc_mem_cs hl hv)
    · exact λ b hb ↦ by simpa using List.all_eq_true.mp hcond b hb
  · rw [if_neg hcond] at heq
    cases heq

-- A rule's head, grounded by a substitution confined to `p.consts` on the
-- rule's own variables, lands in the Herbrand base — the fact common to
-- every evaluator's "stays within the base" proof, however it produces σ.
theorem Program.grounded_head_mem_herbrand_base {p: Program} {r: Rule} {σ: Subst}
    (hr: r ∈ p) (hcs: ∀ v ∈ r.vars, σ v ∈ p.consts):
    Subst.grounded r.head σ ∈ p.herbrand_base
:= by
  refine List.mem_flatMap.mpr ⟨r.head, List.mem_flatMap.mpr ⟨r, hr, .head _⟩, ?_⟩
  refine Atom.mem_groundings (λ v hv ↦ hcs v ?_)
  obtain ⟨b, hb, hbv⟩ := r.safe v hv
  exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hbv⟩)

-- ...and so lands in the Herbrand base, which is what bounds the loop.
theorem Program.stepAtoms_mem_herbrand_base {p: Program}
    {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.stepAtoms kb →
    a ∈ p.herbrand_base
:= by
  intro ha
  obtain ⟨r, hr, σ, hcs, _, rfl⟩ := Program.mem_stepAtoms ha
  exact Program.grounded_head_mem_herbrand_base hr hcs

-- A substitution that fires `r` against `kb` can only have used constants
-- from `p.consts`, provided `kb` itself respects the Herbrand bound: each
-- body atom lands in `kb`, hence in the base, and the base introduces no
-- constants the program does not already mention.
theorem Program.subst_consts {p: Program} {r: Rule} {σ: Subst}
    {kb: List GrAtom}:
    (∀ g ∈ kb, g ∈ p.herbrand_base) →
    (∀ b ∈ r.body, Subst.grounded b σ ∈ kb) →
    ∀ v ∈ r.vars, σ v ∈ p.consts
:= by
  intro hbound hbody v hv
  obtain ⟨b, hb, hbv⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hv)
  refine Program.consts_of_mem_herbrand_base (hbound _ (hbody b hb)) _ ?_
  exact Atom.mem_consts.mpr (List.mem_map.mpr ⟨.inl v, Atom.mem_vars.mp hbv, rfl⟩)

-- COMPLETENESS: if ANY substitution fires `r` against `kb`, the enumeration
-- already produced that head. This is the payoff of enumerating rather than
-- matching, and it rests on `subst_consts` above plus `Atom.ground_congr`:
-- the candidate agreeing with `σ` on `r.vars` grounds `r` identically.
theorem Program.mem_stepAtoms_of_fires {p: Program} {r: Rule} {σ: Subst}
    {kb: List GrAtom}:
    r ∈ p →
    (∀ g ∈ kb, g ∈ p.herbrand_base) →
    (∀ b ∈ r.body, Subst.grounded b σ ∈ kb) →
    Subst.grounded r.head σ ∈ p.stepAtoms kb
:= by
  intro hr hbound hbody
  have hcs := Program.subst_consts hbound hbody
  have hlmem: r.vars.map (λ v ↦ (v, σ v))
      ∈ Variable.assignments r.vars p.consts.eraseDups :=
    Variable.assignments_complete (λ v hv ↦ List.mem_eraseDups.mpr (hcs v hv))
  have hagree: ∀ v ∈ r.vars, Subst.ofAssoc (r.vars.map (λ v ↦ (v, σ v))) v = σ v :=
    λ v hv ↦ Subst.ofAssoc_map hv
  have hbodyeq: ∀ b ∈ r.body,
      Subst.grounded b (Subst.ofAssoc (r.vars.map (λ v ↦ (v, σ v))))
        = Subst.grounded b σ :=
    λ b hb ↦ Subtype.ext (Atom.ground_congr (λ v hv ↦
      hagree v (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hv⟩))))
  have hheadeq: Subst.grounded r.head (Subst.ofAssoc (r.vars.map (λ v ↦ (v, σ v))))
      = Subst.grounded r.head σ := by
    refine Subtype.ext (Atom.ground_congr (λ v hv ↦ ?_))
    obtain ⟨b, hb, hbv⟩ := r.safe v hv
    exact hagree v (List.mem_eraseDups.mpr
      (List.mem_flatMap.mpr ⟨b, hb, hbv⟩))
  have hcond: r.body.all (λ b ↦
      decide (Subst.grounded b (Subst.ofAssoc (r.vars.map (λ v ↦ (v, σ v)))) ∈ kb))
      = true := by
    refine List.all_eq_true.mpr (λ b hb ↦ ?_)
    simp only [decide_eq_true_iff, hbodyeq b hb]
    exact hbody b hb
  refine List.mem_flatMap.mpr ⟨r, hr, List.mem_filterMap.mpr
    ⟨_, List.mem_map.mpr ⟨_, hlmem, rfl⟩, ?_⟩⟩
  rw [if_pos hcond, hheadeq]

-- Saturation computes the model.
