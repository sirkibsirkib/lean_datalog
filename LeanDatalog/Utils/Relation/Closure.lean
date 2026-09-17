abbrev Rel α β := α → β → Prop

example (T: Type): Rel T T := Eq
def all_nat: Rel Nat Nat := λ _ _ ↦ True

example: all_nat 5 3 := by
  unfold all_nat
  exact True.intro

abbrev EndoRel α := Rel α α

example: EndoRel Nat := all_nat


namespace Function

-- The reflexive-transitive closure of `r`; in Datalog,
--   r*(X, X).   r*(X, Z) :- r*(X, Y), r(Y, Z).
inductive ReflTransGen {α: Type} (r: EndoRel α): EndoRel α where
  | refl x:
      ReflTransGen r x x

  | snoc x y z:
      ReflTransGen r x y →
               r y z →
      ReflTransGen r x z

example: EndoRel Nat → EndoRel Nat := ReflTransGen
example: EndoRel Nat := ReflTransGen all_nat

example: ReflTransGen all_nat 6 6 := ReflTransGen.refl 6
example :=
  let h1: ReflTransGen all_nat 5 5 := .refl 5
  let h2:              all_nat 6 6 := .intro
  (.snoc 5 5 6 h1 h2: ReflTransGen all_nat 5 6)

-- Zero or one step.
inductive ReflGen {α: Type} (r: EndoRel α): EndoRel α where
  | refl x:
      ReflGen r x x

  | single x y:
      r x y →
      ReflGen r x y

theorem ReflGen.toReflTransGen {α: Type} {r: EndoRel α} {x y: α}:
    r.ReflGen x y →
    r.ReflTransGen x y
:= by
  intro h
  cases h with
  | refl _ => exact .refl _
  | single _ _ hstep => exact .snoc _ _ _ (.refl _) hstep

theorem ReflTransGen.single {α: Type} {r: EndoRel α} {x y: α}:
    r x y →
    r.ReflTransGen x y
:= snoc x x y (.refl x)

theorem ReflTransGen.trans {α: Type} {r: EndoRel α} {x y z: α}:
    r.ReflTransGen x y →
    r.ReflTransGen y z →
    r.ReflTransGen x z
:= by
  intro hxy hyz
  induction hyz with
  | refl _ => exact hxy
  | snoc _ _ _ _ hstep ih => exact snoc _ _ _ (ih hxy) hstep

end Function
