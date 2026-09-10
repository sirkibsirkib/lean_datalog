abbrev Rel α β := α → β → Prop
abbrev EndoRel α := Rel α α

/-
The reflexive-transitive and reflexive closures of a relation, and just
enough API to chain steps together.
-/

namespace Function

inductive ReflTransGen {α: Type} (r: EndoRel α): EndoRel α where
  | refl x:
      ReflTransGen r x x

  | scoc x y z:
      ReflTransGen r x y →
               r y z →
      ReflTransGen r x z

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
  | single _ _ hstep => exact .scoc _ _ _ (.refl _) hstep

theorem ReflTransGen.single {α: Type} {r: EndoRel α} {x y: α}:
    r x y →
    r.ReflTransGen x y
:= .scoc x x y (.refl x)

theorem ReflTransGen.trans {α: Type} {r: EndoRel α} {x y z: α}:
    r.ReflTransGen x y →
    r.ReflTransGen y z →
    r.ReflTransGen x z
:= by
  intro hxy hyz
  induction hyz with
  | refl _ => exact hxy
  | scoc _ _ _ _ hstep ih => exact .scoc _ _ _ (ih hxy) hstep

end Function
