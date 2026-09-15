abbrev Rel α β := α → β → Prop

example: Rel Nat Nat := λ m n ↦ m = n
def all_nat: Rel Nat Nat := λ _ _ ↦ True

example: all_nat 5 3 := by
  unfold all_nat
  exact True.intro

abbrev EndoRel α := Rel α α

/-
The reflexive-transitive and reflexive closures of a relation, and just
enough API to chain steps together.
-/

namespace Function

inductive ReflTransGen {α: Type} (r: EndoRel α): EndoRel α where
  | refl x:
      ReflTransGen r x x

  | snoc x y z:
      ReflTransGen r x y →
               r y z →
      ReflTransGen r x z

-- r(X,Z) :- r(X,Y), r(Y,Z)

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
