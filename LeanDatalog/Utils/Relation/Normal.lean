import LeanDatalog.Utils.Relation.Confluence

/-
Normal forms, and normalisation: confluence gives UNIQUENESS of normal
forms, termination gives EXISTENCE. The two halves are independent, and
only the second needs to know anything about the relation's size.
-/

namespace Function

-- Nothing applies any more.
def Normal {α: Type} (r: EndoRel α) (x: α): Prop :=
  ¬ ∃ y, r x y

-- A normal form reduces only to itself.
theorem Normal.eq_of_reflTransGen {α: Type} {r: EndoRel α} {x y: α}:
    r.Normal x →
    r.ReflTransGen x y →
    x = y
:= by
  intro hn h
  induction h with
  | refl _ => rfl
  | snoc _ a y _ hstep ih =>
    have hxa := ih hn
    subst hxa
    exact absurd ⟨y, hstep⟩ hn

-- Confluence ALONE forces normal forms to be unique. Nothing here needs to
-- know that the relation terminates.
theorem Confluent.normal_unique {α: Type} {r: EndoRel α} {x y z: α}:
    r.Confluent →
    r.ReflTransGen x y → r.Normal y →
    r.ReflTransGen x z → r.Normal z →
    y = z
:= by
  intro hc hxy hny hxz hnz
  obtain ⟨w, hyw, hzw⟩ := hc x y z hxy hxz
  rw [hny.eq_of_reflTransGen hyw, hnz.eq_of_reflTransGen hzw]

-- No infinite reduction sequence: the step relation, read backwards, is
-- well-founded.
def Terminating {α: Type} (r: EndoRel α): Prop :=
  WellFounded (λ y x ↦ r x y)

-- Accessibility of the STARTING POINT is all that existence needs. This is
-- the form to reach for when a relation runs forever from some unreachable
-- starting points but not from the one actually of interest — global
-- well-foundedness is a strictly stronger demand.
theorem _root_.Acc.exists_normal {α: Type} {r: EndoRel α} {x: α}:
    Acc (λ y x ↦ r x y) x →
    ∃ y, r.ReflTransGen x y ∧ r.Normal y
:= by
  intro h
  induction h with
  | intro x _ ih =>
    by_cases hn: ∃ y, r x y
    · obtain ⟨y, hxy⟩ := hn
      obtain ⟨z, hyz, hnz⟩ := ih y hxy
      exact ⟨z, (ReflTransGen.single hxy).trans hyz, hnz⟩
    · exact ⟨x, .refl _, hn⟩

-- Termination ALONE forces normal forms to exist, everywhere at once.
theorem Terminating.exists_normal {α: Type} {r: EndoRel α}:
    r.Terminating →
    ∀ x, ∃ y, r.ReflTransGen x y ∧ r.Normal y
:= λ ht x ↦ Acc.exists_normal (ht.apply x)

-- The usual way to establish accessibility: an invariant `P` that steps
-- preserve, and a `Nat` measure that steps strictly decrease. Only elements
-- satisfying `P` are reached, which is what makes this usable for relations
-- that misbehave elsewhere.
theorem acc_of_measure {α: Type} {r: EndoRel α} {P: α → Prop} {m: α → Nat}
    (hpres: ∀ x y, P x → r x y → P y)
    (hdec:  ∀ x y, P x → r x y → m y < m x):
  ∀ {x}, P x → Acc (λ y x ↦ r x y) x
:= by
  have go: ∀ n x, m x ≤ n → P x → Acc (λ y x ↦ r x y) x := by
    intro n
    induction n with
    | zero =>
      intro x hle hx
      refine .intro x (λ y hy ↦ ?_)
      exact absurd (Nat.lt_of_lt_of_le (hdec x y hx hy) hle) (Nat.not_lt_zero _)
    | succ n ih =>
      intro x hle hx
      refine .intro x (λ y hy ↦ ?_)
      exact ih y
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (hdec x y hx hy) hle))
        (hpres x y hx hy)
  intro x hx
  exact go (m x) x (Nat.le_refl _) hx

-- Both halves together: every element reduces to exactly one normal form.
def Normalising {α: Type} (r: EndoRel α): Prop :=
  r.Terminating ∧ r.Confluent

theorem Normalising.exists_normal {α: Type} {r: EndoRel α}:
    r.Normalising →
    ∀ x, ∃ y, r.ReflTransGen x y ∧ r.Normal y
:= λ h ↦ h.1.exists_normal

theorem Normalising.normal_unique {α: Type} {r: EndoRel α} {x y z: α}:
    r.Normalising →
    r.ReflTransGen x y → r.Normal y →
    r.ReflTransGen x z → r.Normal z →
    y = z
:= λ h ↦ h.2.normal_unique

end Function
