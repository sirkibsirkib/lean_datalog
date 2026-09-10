
abbrev Set (α: Sort u) := α → Prop

-- `EmptyCollection` and `Union` are classes over `Type u`, so these instances
-- are one universe less general than `Set`, which accepts any `Sort`. The
-- `Singleton` instance is likewise pinned by its `outParam (Type u)`.
instance {α: Type u}: EmptyCollection (Set α) where
  emptyCollection _ := False

example: Set Nat := ∅
example: Set Nat := {}

instance {α}: Singleton α (Set α) where
  singleton := Eq

example: Set Nat := {1}
example: Set Nat := {5}
example: Set String := {"howdy"}

instance {α: Type u}: Union (Set α) where
  union s1 s2 a := s1 a ∨ s2 a

example: Set Nat := {1} ∪ {2}

instance {α: Type u}: HasSubset (Set α) where
  Subset small large := ∀ a, small a → large a

theorem Set.subset_refl:
  ∀ {α: Type u} (s: Set α),
    s ⊆ s
:= λ _ _ h ↦ h

instance {α}: Membership α (Set α) where
  mem s a := s a

-- Membership is decidable exactly when the underlying predicate is. Instance
-- search will not unfold the `Membership` instance to discover this on its
-- own, so this bridge is what lets a set with a decidable predicate drive
-- `decide` and `if` — no separate `α → Bool` notion of set is needed.
instance {α: Type u} (s: Set α) [d: DecidablePred s] (a: α): Decidable (a ∈ s) := d a

theorem Set.union_empty:
  ∀ α (s: Set α),
    s ∪ ∅ = s
  ∧ ∅ ∪ s = s
:= by
  intro α s
  constructor
    <;> funext a
    <;> simp [Union.union, EmptyCollection.emptyCollection]

instance {α: Type u}: Insert α (Set α) where
  insert a s := s ∪ {a}


example: Set Nat := {1,2,3}

example {α} {a b: α}: a ∈ ({a,b}: Set α) := by
  simp [Membership.mem, Singleton.singleton, Insert.insert, Union.union]

theorem Set.mem_union_symm:
  ∀ α (s1 s2: Set α) a,
    a ∈ s1 ∪ s2 →
    a ∈ s2 ∪ s1
:= by
  simp [Union.union, Membership.mem]
  intro α s1 s2 a h
  exact h.symm

theorem Set.insert_idemp:
  ∀ α (s: Set α) a,
    a ∈ s →
    a ∈ (Insert.insert a s)
:= by
  intro α s a h
  simp [Membership.mem, Insert.insert, Union.union, Singleton.singleton]

theorem Set.mem_insert:
  ∀ {α: Type u} {s: Set α} {a x: α},
    x ∈ insert a s ↔ x ∈ s ∨ a = x
:= Iff.rfl

theorem Set.subset_insert:
  ∀ {α: Type u} (s: Set α) (a: α),
    s ⊆ insert a s
:= λ _ _ _ h ↦ Or.inl h

-- Inserting in either order lands in the same set. Needs `propext`: the two
-- sides are different predicates that happen to be pointwise equivalent.
theorem Set.insert_comm:
  ∀ {α: Type u} (s: Set α) (a b: α),
    insert a (insert b s) = insert b (insert a s)
:= by
  intro α s a b
  funext x
  apply propext
  constructor
    <;> rintro ((h | h) | h)
    <;> first
      | exact Or.inl (Or.inl h)
      | exact Or.inl (Or.inr h)
      | exact Or.inr h

-- The examples above only check that the notation elaborates; these pin down
-- what it means, since `Set Nat := ∅` would accept any set whatsoever.
example (n: Nat): (∅: Set Nat) n = False := rfl
example (s t: Set Nat) (a: Nat): (s ∪ t) a = (s a ∨ t a) := rfl
example (m n: Nat): ({m}: Set Nat) n = (m = n) := rfl

-- Viewing a list as a set: the two shapes a list-backed set grows in.
theorem Set.ofList_nil {α: Type}:
    (λ x ↦ x ∈ ([]: List α)) = (∅: Set α)
:= by
  funext x
  apply propext
  constructor
  · intro h; nomatch h
  · intro h; exact False.elim h

theorem Set.ofList_cons {α: Type} {a: α} {l: List α}:
    (λ x ↦ x ∈ a :: l) = insert a (λ x ↦ x ∈ l)
:= by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | head _ => exact Or.inr rfl
    | tail _ h => exact Or.inl h
  · rintro (h | rfl)
    · exact .tail _ h
    · exact .head _
