/-
General-purpose `List` facts, with no Datalog content — the list-shaped
counterpart to Set.lean and Relation.lean.
-/

-- All ways of choosing one element from each list in `ls`.
def List.choices {α: Type}: List (List α) → List (List α)
  | [] => [[]]
  | l :: ls => l.flatMap λ x ↦ (List.choices ls).map (x :: ·)

-- `choices` really does contain every pointwise selection: if `g` picks,
-- for each `x` of `l`, some element of `f x`, then the list of picks is one
-- of the choices.
theorem List.map_mem_choices {α β: Type} {f: α → List β} {g: α → β}:
  ∀ {l: List α},
    (∀ x ∈ l, g x ∈ f x) →
    l.map g ∈ List.choices (l.map f)
:= by
  intro l
  induction l with
  | nil => intro _; exact .head _
  | cons a l ih =>
    intro h
    simp only [List.map, List.choices, List.mem_flatMap, List.mem_map]
    exact ⟨g a, h a (.head _), l.map g, ih (λ x hx ↦ h x (.tail _ hx)), rfl⟩

-- The soundness direction: nothing appears in a choice that did not come
-- out of one of the lists chosen from. Positional correspondence would be
-- true too, but "came from some list" is all callers here need.
theorem List.mem_choices_mem {α β: Type} {f: α → List β}:
  ∀ {l: List α} {ys: List β},
    ys ∈ List.choices (l.map f) →
    ∀ y ∈ ys, ∃ x ∈ l, y ∈ f x
:= by
  intro l
  induction l with
  | nil =>
    intro ys hys y hy
    simp only [List.map, List.choices, List.mem_singleton] at hys
    subst hys
    cases hy
  | cons a l ih =>
    intro ys hys y hy
    simp only [List.map, List.choices, List.mem_flatMap, List.mem_map] at hys
    obtain ⟨b, hb, zs, hzs, rfl⟩ := hys
    cases hy with
    | head _ => exact ⟨a, .head _, hb⟩
    | tail _ hy =>
      obtain ⟨x, hx, hyx⟩ := ih hzs y hy
      exact ⟨x, .tail _ hx, hyx⟩

-- Strict version of core's `List.countP_mono_left`: if `q` implies `p`
-- throughout `l` and some element satisfies `p` but not `q`, the count
-- strictly drops.
theorem List.countP_lt_countP {α: Type} {p q: α → Bool} {a: α}:
  ∀ {l: List α},
    (∀ x ∈ l, q x → p x) →
    a ∈ l →
    p a →
    ¬ q a →
    l.countP q < l.countP p
:= by
  intro l
  induction l with
  | nil => intro _ ha _ _; cases ha
  | cons b l ih =>
    intro himp ha hpa hqa
    have hqa': q a = false := by
      cases h: q a with
      | false => rfl
      | true => exact absurd h hqa
    have hle: l.countP q ≤ l.countP p :=
      List.countP_mono_left (λ x hx ↦ himp x (.tail _ hx))
    rw [List.countP_cons, List.countP_cons]
    cases ha with
    | head _ =>
      simp only [hpa, hqa', if_true, Bool.false_eq_true, if_false]
      omega
    | tail _ ha =>
      have hlt := ih (λ x hx ↦ himp x (.tail _ hx)) ha hpa hqa
      by_cases hqb: q b = true
      · have hpb := himp b (.head _) hqb
        simp only [hqb, hpb, if_true]
        omega
      · have hqb': q b = false := by
          cases h: q b with
          | false => rfl
          | true => exact absurd h hqb
        simp only [hqb', Bool.false_eq_true, if_false]
        omega
