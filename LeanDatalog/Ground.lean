import LeanDatalog.Syntax

-- Applying a substitution turns a rule as written into a rule instance.
abbrev Subst: Type := Variable → Constant

-- Syntax that can be ground: a decidable "has no variables", and a
-- substitution whose result always has none.
class Groundable (T: Type) where
  grounded: T → Bool
  ground: Subst → T → T
  ground_grounded: ∀ σ t, grounded (ground σ t)
  ground_idemp:    ∀ σ t, ground σ (ground σ t) = ground σ t

abbrev Grounded  (T: Type) [i: Groundable T] := { t // i.grounded t }

-- Argument order flipped for dot notation: `σ.ground t`.
def Subst.ground {T: Type} [i: Groundable T] (t: T) (σ: Subst): T :=
  i.ground σ t

def Subst.grounded {T: Type} [i: Groundable T] (t: T) (σ: Subst): Grounded T :=
  ⟨i.ground σ t, i.ground_grounded σ t⟩

instance: Groundable Arg where
  grounded := Sum.isRight

  ground σ
  | .inl v => .inr (σ v)
  | .inr c => .inr c

  ground_grounded σ a := by cases a <;> rfl

  ground_idemp σ a := by cases a <;> simp

instance: Groundable Atom where
  grounded a := a.args.all Groundable.grounded

  ground σ a := {
    pred := a.pred,
    args := a.args.map σ.ground
  }

  ground_grounded σ a := by
    simp
    intro arg h
    apply Groundable.ground_grounded

  ground_idemp σ a := by
    simp
    intro arg h
    apply Groundable.ground_idemp

instance: Groundable Rule where
  grounded r :=
    Groundable.grounded r.head
    ∧ r.body.all Groundable.grounded

  ground σ r := {
    head := σ.ground r.head,
    body := r.body.map σ.ground
    safe := by
      intro v hv
      obtain ⟨arg, _, harg⟩ := List.mem_map.mp (Atom.mem_vars.mp hv)
      have hg := Groundable.ground_grounded σ arg
      unfold Subst.ground at harg
      rw [harg] at hg
      simp [Groundable.grounded] at hg
  }

  ground_grounded σ r := by
    simp
    constructor
    . apply Groundable.ground_grounded
    . intro a h
      apply Groundable.ground_grounded

  ground_idemp σ r := by
    simp
    constructor
    . apply Groundable.ground_idemp
    . intro a h
      apply Groundable.ground_idemp

abbrev GrAtom := Grounded Atom
