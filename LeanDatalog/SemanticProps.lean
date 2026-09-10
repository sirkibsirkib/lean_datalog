import LeanDatalog.Semantics
import LeanDatalog.Herbrand

/-
Facts *about* `Program.infer`, as opposed to Semantics.lean, which states
it: that it is confluent, that a program therefore has at most one model,
and that inference from ∅ terminates, so it has at least one.
-/

-- Inference never leaves the Herbrand base. This is the one lemma joining
-- the Herbrand machinery to the semantics.
--
-- It is where `Rule.safe` earns its keep. Every variable of the head also
-- occurs in the body; the body atoms are already known; known atoms carry
-- only `p.consts`; so every constant the substitution can put in the head
-- is one the base already enumerates. Drop range restriction and the claim
-- collapses: `p(X) :- q(a).` fires under every substitution at all.
theorem Program.infer_mem_herbrand_base {p: Program} {kb kb': Kb}:
    (∀ a ∈ kb, a ∈ p.herbrand_base) →
    p.infer kb kb' →
    ∀ a ∈ kb', a ∈ p.herbrand_base
:= by
  rintro hkb ⟨r, hr, σ, hfires, _, rfl⟩ a ha
  rcases ha with h | rfl
  · exact hkb a h
  · refine List.mem_flatMap.mpr ⟨r.head, List.mem_flatMap.mpr ⟨r, hr, .head _⟩, ?_⟩
    refine Atom.mem_groundings ?_
    intro v hv
    obtain ⟨ba, hba, hbav⟩ := r.safe v hv
    refine Program.consts_of_mem_herbrand_base (hkb _ (hfires ba hba)) _ ?_
    exact Atom.mem_consts.mpr (List.mem_map.mpr ⟨.inl v, Atom.mem_vars.mp hbav, rfl⟩)


/-
Confluence: the order in which rules fire cannot change where you end up.
-/

-- Datalog is monotone: adding to a knowledge base never stops a rule from
-- firing. Everything below rests on this, and negation is exactly what
-- would destroy it.
theorem Rule.fires_mono:
  ∀ {r: Rule} {σ: Subst} {kb kb': Kb},
    kb ⊆ kb' →
    r.fires σ kb →
    r.fires σ kb'
:= λ hsub hfires a ha ↦ hsub _ (hfires a ha)

-- Two single steps out of the same knowledge base always reconcile, in AT
-- MOST one further step each: whichever rule fired second is still
-- available after the first, precisely by monotonicity. Closing the square
-- this tightly is what buys full confluence below without needing to know
-- that inference terminates.
theorem Program.infer_semiDiamond (p: Program):
    p.infer.SemiDiamond
:= by
  intro kb kb₁ kb₂ h₁ h₂
  obtain ⟨r₁, hr₁, σ₁, hf₁, hnew₁, rfl⟩ := h₁
  obtain ⟨r₂, hr₂, σ₂, hf₂, hnew₂, rfl⟩ := h₂
  by_cases hsame: σ₁.grounded r₁.head = σ₂.grounded r₂.head
  · -- both steps added the same atom, so they already agree: zero steps
    exact ⟨_, .refl _, by rw [hsame]; exact .refl _⟩
  · -- distinct atoms: each step survives the other, so one step each
    refine ⟨insert (σ₂.grounded r₂.head) (insert (σ₁.grounded r₁.head) kb),
      .single _ _ ⟨r₂, hr₂, σ₂, ?_, ?_, rfl⟩,
      .single _ _ ⟨r₁, hr₁, σ₁, ?_, ?_, ?_⟩⟩
    · exact Rule.fires_mono (Set.subset_insert _ _) hf₂
    · rintro (h | h)
      · exact hnew₂ h
      · exact hsame h
    · exact Rule.fires_mono (Set.subset_insert _ _) hf₁
    · rintro (h | h)
      · exact hnew₁ h
      · exact hsame h.symm
    · exact Set.insert_comm kb _ _

-- The payoff: however you schedule rule firings, any two runs can still be
-- driven back together. No two maximal runs can reach different answers.
theorem Program.infer_confluent (p: Program):
    p.infer.Confluent
:= p.infer_semiDiamond.confluent

theorem Program.infer_locallyConfluent (p: Program):
    p.infer.LocallyConfluent
:= p.infer_semiDiamond.locallyConfluent


/-
Normalisation. Confluence above already delivers half of it: `model` is
literally "a normal form of `infer` reached from the empty knowledge base",
so uniqueness of models falls out with no termination argument at all.
-/

-- A program has AT MOST one model — proved from confluence alone.
theorem Program.model_unique (p: Program) {kb kb': Kb}:
    p.model kb →
    p.model kb' →
    kb = kb'
:= by
  intro ⟨hreach, hsat⟩ ⟨hreach', hsat'⟩
  exact p.infer_confluent.normal_unique hreach hsat hreach' hsat'

-- Every step strictly grows the knowledge base.
--
-- This is as far as termination gets without a finiteness bound, and it is
-- NOT far enough: a strictly increasing chain of sets can be infinite. It
-- is infinite here in the worst case, because `Constant` is infinite (any
-- lowercase-initial string), so there are infinitely many ground atoms
-- available to add one at a time. Bounding the reachable atoms by
-- `herbrand_base` is precisely what rules that out.
theorem Program.infer_grows (p: Program) {kb kb': Kb}:
    p.infer kb kb' →
    kb ⊆ kb' ∧ ∃ a, a ∉ kb ∧ a ∈ kb'
:= by
  rintro ⟨r, _, σ, _, hnew, rfl⟩
  exact ⟨Set.subset_insert _ _, σ.grounded r.head, hnew, Or.inr rfl⟩

/-
Termination.

The goal below is accessibility of ∅, not `p.infer.Terminating`. The
latter would say `infer` is well founded on ALL of `Kb`, and that is false:
take `p = [ q(X) :- p(X). ]` — a safe rule — and the knowledge base
`{ p(c) : c any constant }`, which is a perfectly good `Set`. The rule
fires for every one of the infinitely many constants, each time adding a
new `q(c)`, so that knowledge base admits an infinite chain. Nothing bounds
a `Kb` that was never built by inference.

What is true, and all that `model_exists` needs, is accessibility of the
starting point ∅ — which does respect the Herbrand bound, vacuously. The
bound is carried along as an invariant, with the count of base atoms not
yet known as the measure.
-/

-- The invariant: everything known is drawn from the Herbrand base.
def Program.Bounded (p: Program) (kb: Kb): Prop :=
  ∀ a ∈ kb, a ∈ p.herbrand_base

-- The measure: how many Herbrand-base atoms remain unknown. Classical,
-- because `Kb` is `Prop`-valued and so has no decision procedure — free
-- here, since `Acc` is a `Prop` and this only ever appears inside proofs.
open Classical in
noncomputable def Program.unseen (p: Program) (kb: Kb): Nat :=
  p.herbrand_base.countP λ a ↦ decide (a ∉ kb)

open Classical in
theorem Program.unseen_lt {p: Program} {kb kb': Kb}:
    p.Bounded kb →
    p.infer kb kb' →
    p.unseen kb' < p.unseen kb
:= by
  intro hb hstep
  obtain ⟨r, _, σ, _, hnew, rfl⟩ := hstep
  refine List.countP_lt_countP (a := σ.grounded r.head) ?_ ?_ ?_ ?_
  · -- still-unknown afterwards implies still-unknown before
    intro x _ hx
    simp only [decide_eq_true_iff] at hx ⊢
    exact λ hmem ↦ hx (Set.subset_insert _ _ x hmem)
  · -- the new atom lies in the base
    exact Program.infer_mem_herbrand_base hb
      ⟨r, ‹_›, σ, ‹_›, hnew, rfl⟩ _ (Or.inr rfl)
  · -- it was unknown before
    simpa using hnew
  · -- and is known afterwards
    simp only [decide_eq_true_iff, not_not]
    exact Or.inr rfl

theorem Program.bounded_empty (p: Program): p.Bounded ∅ := by
  intro a ha
  cases ha

theorem Program.acc_empty (p: Program):
    Acc (λ kb' kb ↦ p.infer kb kb') ∅
:= Function.acc_of_measure
    (P := p.Bounded) (m := p.unseen)
    (λ _ _ hb hstep ↦ Program.infer_mem_herbrand_base hb hstep)
    (λ _ _ hb hstep ↦ Program.unseen_lt hb hstep)
    p.bounded_empty

-- Existence of a model, the other half of `model_unique` above. Together
-- they say: every program has exactly one model.
theorem Program.model_exists (p: Program):
    ∃ kb, p.model kb
:= p.acc_empty.exists_normal
