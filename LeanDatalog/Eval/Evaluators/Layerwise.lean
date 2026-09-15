import LeanDatalog.Eval.Step
import LeanDatalog.Eval.Interface

/-
Saturation one layer at a time — textbook naive evaluation.

Each tick consumes a whole round of consequences rather than a single atom,
so after `k` ticks the knowledge base holds exactly the atoms whose
SHORTEST derivation has depth `k` or less:

  tick 1 ─▸ ● ● ● ●     everything the facts alone yield
  tick 2 ─▸ ● ● ●       everything those yield in turn
  tick 3 ─▸ ● ●
  tick 4 ─▸ ●

The number of ticks is therefore the depth of the fixpoint rather than the
number of atoms derived — four here where Stepwise.lean would take ten.

How much that saves is a property of the program, not of this file. A chain
of rules like `p. q :- p. r :- q.` has one atom per layer and saves
nothing, while non-linear recursion (`t(X,Y), t(Y,Z)`) doubles path lengths
each round, reaching depth `log n` over `n²` atoms.

Per tick the work is the same as Stepwise's: `stepAtoms` is shared between
them and still tries every candidate substitution, so consuming rounds
rather than atoms is the only difference between the two.
-/

namespace Layerwise

-- One round: every consequence not already known. Deduplicated, so a `kb`
-- grown from `[]` never repeats an atom even when several substitutions
-- derive it — which keeps membership tests honest and the output clean.
def round (p: Program) (kb: List GrAtom): List GrAtom :=
  ((p.stepAtoms kb).filter λ a ↦ decide (a ∉ kb)).eraseDups

-- A round holds exactly the consequences that are not already known;
-- `eraseDups` and `filter` are visible to membership in neither direction.
theorem mem_round {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ round p kb ↔ a ∈ p.stepAtoms kb ∧ a ∉ kb
:= by
  constructor
  · intro ha
    have h := List.mem_filter.mp (List.mem_eraseDups.mp ha)
    exact ⟨h.1, by simpa using h.2⟩
  · intro ⟨ha, hnew⟩
    exact List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨ha, by simpa using hnew⟩)

-- One tick per layer. Writing M for the size of the model, D for the depth
-- of the fixpoint and W for the largest round before deduplication (see
-- Step.lean for the rest of the parameters):
--
--   ticks = D        total  Θ(P·B·A · C^V · M · D)  +  Θ(W² · A)
--
-- The first term is Stepwise's with one factor of M replaced by D, which is
-- the whole of the saving: D ≤ M always, and D ≪ M whenever layers are wide.
-- The second term is `eraseDups`, quadratic in the round size, and the one
-- cost here that Stepwise does not pay.
def saturateGo (p: Program) (kb: List GrAtom): List GrAtom :=
  match _hround: round p kb with
  | [] => kb
  | a :: rest => saturateGo p ((a :: rest) ++ kb)
termination_by p.herbrand_base.countP λ b ↦ decide (b ∉ kb)
decreasing_by
  have ha: a ∈ round p kb := by rw [_hround]; exact .head _
  obtain ⟨hstep, hnew⟩ := mem_round.mp ha
  refine List.countP_lt_countP (a := a)
    ?_ (Program.stepAtoms_mem_herbrand_base hstep) ?_ ?_
  · -- unknown after the batch implies unknown before it
    intro x _ hx
    simp only [decide_eq_true_iff] at hx ⊢
    exact λ hg ↦ hx (List.mem_append_right _ hg)
  · -- `a` was unknown before
    simpa using hnew
  · -- ...and is known now, since `a` heads the batch
    simp only [decide_eq_true_iff]
    exact λ h ↦ h (.head _)

def saturate (p: Program): List GrAtom :=
  saturateGo p []

-- The loop returns only at a fixpoint: an empty round means every
-- consequence of the knowledge base is already in it.
theorem saturateGo_fixpoint (p: Program):
  ∀ kb, ∀ a ∈ p.stepAtoms (saturateGo p kb), a ∈ saturateGo p kb
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hround =>
    rw [saturateGo.eq_def, hround]
    intro a ha
    by_cases hmem: a ∈ kb
    · exact hmem
    · have := mem_round.mpr ⟨ha, hmem⟩
      rw [hround] at this
      cases this
  | case2 kb a rest hround ih =>
    rw [saturateGo.eq_def, hround]
    exact ih

theorem saturateGo_bounded (p: Program):
  ∀ kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    ∀ g ∈ saturateGo p kb, g ∈ p.herbrand_base
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hround =>
    intro hb
    rw [saturateGo.eq_def, hround]
    exact hb
  | case2 kb a rest hround ih =>
    intro hb
    rw [saturateGo.eq_def, hround]
    refine ih (λ g hg ↦ ?_)
    rcases List.mem_append.mp hg with hg | hg
    · have hr: g ∈ round p kb := by rw [hround]; exact hg
      exact Program.stepAtoms_mem_herbrand_base (mem_round.mp hr).1
    · exact hb g hg

-- Adding a whole batch is a SEQUENCE of `infer` steps, one per atom of the
-- batch. Each remains licensed after the earlier ones have been added,
-- because its body atoms sat in `kb`, which only grows; and an atom that
-- some earlier atom of the batch already introduced needs no step at all,
-- since adding it leaves the set alone.
theorem reachable_append (p: Program) (kb: List GrAtom):
  ∀ l: List GrAtom,
    (∀ a ∈ l, a ∈ p.stepAtoms kb) →
    p.infer.ReflTransGen (λ g ↦ g ∈ kb) (λ g ↦ g ∈ l ++ kb)
:= by
  intro l
  induction l with
  | nil => intro _; exact .refl _
  | cons a l ih =>
    intro hl
    have hrest := ih (λ x hx ↦ hl x (.tail _ hx))
    by_cases hmem: a ∈ l ++ kb
    · -- already derived earlier in this same batch: the set does not change
      have heq: (λ g ↦ g ∈ a :: l ++ kb) = (λ g: GrAtom ↦ g ∈ l ++ kb) := by
        funext x
        apply propext
        constructor
        · intro hx
          cases hx with
          | head _ => exact hmem
          | tail _ hx => exact hx
        · intro hx; exact .tail _ hx
      rw [heq]
      exact hrest
    · refine .snoc _ _ _ hrest ?_
      obtain ⟨r, hr, σ, _, hbody, rfl⟩ := Program.mem_stepAtoms (hl a (.head _))
      exact ⟨r, hr, σ, λ b hb ↦ List.mem_append_right _ (hbody b hb),
        hmem, Set.ofList_cons⟩

theorem saturateGo_reachable (p: Program):
  ∀ kb, p.infer.ReflTransGen ∅ (λ g ↦ g ∈ kb) →
    p.infer.ReflTransGen ∅ (λ g ↦ g ∈ saturateGo p kb)
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hround =>
    intro h
    rw [saturateGo.eq_def, hround]
    exact h
  | case2 kb a rest hround ih =>
    intro h
    rw [saturateGo.eq_def, hround]
    refine ih (h.trans (reachable_append p kb (a :: rest) (λ x hx ↦ ?_)))
    have hr: x ∈ round p kb := by rw [hround]; exact hx
    exact (mem_round.mp hr).1

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

end Layerwise
