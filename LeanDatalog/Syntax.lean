import LeanDatalog.Utils.String

abbrev Constant := { s: String // s.first_with Char.isLower }
abbrev Variable := { s: String // s.first_with Char.isUpper }

abbrev Arg := Variable ⊕ Constant

structure Atom where
  pred: Constant
  args: List Arg
deriving Repr, DecidableEq

def Atom.vars (a: Atom): List Variable :=
  a.args.filterMap λ
    | .inl v => some v
    | .inr _ => none

-- What `vars` amounts to on `args`, so callers need not unfold the
-- `filterMap` and case-split on `Arg` themselves.
theorem Atom.mem_vars {a: Atom} {v: Variable}:
    v ∈ a.vars ↔ (Sum.inl v: Arg) ∈ a.args := by
  simp only [Atom.vars, List.mem_filterMap]
  constructor
  · rintro ⟨arg, harg, heq⟩
    cases arg with
    | inl v' =>
      rw [Option.some.inj heq] at harg
      exact harg
    | inr _ => cases heq
  · intro hv
    exact ⟨.inl v, hv, rfl⟩

def Atom.consts (a: Atom): List Constant :=
  a.args.filterMap λ
    | .inl _ => none
    | .inr c => some c

-- Concrete syntax, the counterpart of Parse.lean: `pred(arg, ...)`. The
-- parens are kept even when there are no arguments, since `p` and `p()`
-- parse to the same atom and the explicit form is less ambiguous to read.
def Atom.toString (a: Atom): String :=
  a.pred.val ++ "(" ++ ", ".intercalate (a.args.map λ
    | .inl v => v.val
    | .inr c => c.val) ++ ")"

instance: ToString Atom := ⟨Atom.toString⟩

-- The counterpart for the constant arguments.
theorem Atom.mem_consts {a: Atom} {c: Constant}:
    c ∈ a.consts ↔ (Sum.inr c: Arg) ∈ a.args := by
  simp only [Atom.consts, List.mem_filterMap]
  constructor
  · rintro ⟨arg, harg, heq⟩
    cases arg with
    | inl _ => cases heq
    | inr c' =>
      rw [Option.some.inj heq] at harg
      exact harg
  · intro h
    exact ⟨.inr c, h, rfl⟩

structure Rule where mk::
  head: Atom
  body: List Atom
  safe: ∀ v,
    v ∈ head.vars →
    ∃ arg,
      arg ∈ body ∧ v ∈ arg.vars
deriving Repr, DecidableEq

abbrev Program := List Rule
