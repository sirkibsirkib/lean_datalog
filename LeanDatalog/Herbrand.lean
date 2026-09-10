import LeanDatalog.Ground
import LeanDatalog.Utils.List

/-
The Herbrand base: the finite set of atoms a program could ever derive.

A Datalog program can only build atoms from the predicates and constants it
already mentions, and there are finitely many of those, so the base is a
finite list. That finiteness is what bounds saturation.

Note what this file does NOT import: nothing here mentions knowledge bases,
inference, or models. The Herbrand base is a fact about a program's syntax
and how substitutions ground it, so this sits BESIDE Semantics.lean rather
than above it. SemanticProps.lean supplies the one lemma that joins the two
(`Program.infer_mem_herbrand_base`).
-/

def Rule.atoms (r: Rule): List Atom := r.head :: r.body

def Program.atoms (p: Program): List Atom := p.flatMap Rule.atoms

-- Every constant symbol mentioned anywhere in `p`: the finite Herbrand
-- universe rules may draw on when their (safe) head/body variables get
-- instantiated.
def Program.consts (p: Program): List Constant :=
  p.atoms.flatMap Atom.consts

-- The constants this argument position can take. Grounding an argument
-- always yields a constant, so working in `Constant` rather than `Arg` is
-- what lets `Atom.groundings` below produce `GrAtom` with no side proof.
def Arg.groundings (a: Arg) (cs: List Constant): List Constant :=
  match a with
  | .inl _ => cs
  | .inr c => [c]

-- ...and the particular constant `σ` puts there.
def Arg.grounding (a: Arg) (σ: Subst): Constant :=
  match a with
  | .inl v => σ v
  | .inr c => c

theorem Arg.ground_eq (a: Arg) (σ: Subst):
    Subst.ground a σ = Sum.inr (a.grounding σ)
:= by cases a <;> rfl

-- An atom whose arguments are all constants is ground, whatever they are.
-- Structural, needing no hypothesis about where the constants came from.
theorem Atom.grounded_of_consts (pred: Constant) (cs: List Constant):
    Groundable.grounded ({ pred, args := cs.map .inr }: Atom)
:= by simp [Groundable.grounded]

-- All ways of grounding `a`'s variables using constants drawn from `cs`.
def Atom.groundings (a: Atom) (cs: List Constant): List GrAtom :=
  (List.choices (a.args.map (Arg.groundings · cs))).map λ consts ↦
    ⟨{ pred := a.pred, args := consts.map .inr }, Atom.grounded_of_consts _ _⟩

-- Grounding one argument lands in that argument's groundings, provided any
-- variable it carries is sent into `cs`. A constant argument is unmoved, so
-- it needs no hypothesis.
theorem Arg.mem_groundings {σ: Subst} {cs: List Constant}:
  ∀ {arg: Arg},
    (∀ v, arg = .inl v → σ v ∈ cs) →
    arg.grounding σ ∈ Arg.groundings arg cs
:= by
  intro arg h
  cases arg with
  | inl v => exact h v rfl
  | inr c => exact .head _

-- Grounding a whole atom lands in that atom's groundings, provided every
-- variable of the atom is sent into `cs`.
theorem Atom.mem_groundings {a: Atom} {σ: Subst} {cs: List Constant}:
    (∀ v ∈ a.vars, σ v ∈ cs) →
    Subst.grounded a σ ∈ Atom.groundings a cs
:= by
  intro h
  refine List.mem_map.mpr ⟨a.args.map (Arg.grounding · σ), List.map_mem_choices ?_, ?_⟩
  · intro arg harg
    refine Arg.mem_groundings ?_
    intro v hv
    subst hv
    exact h v (Atom.mem_vars.mpr harg)
  · refine Subtype.ext ?_
    show (⟨a.pred, _⟩: Atom) = ⟨a.pred, _⟩
    congr 1
    rw [List.map_map]
    exact List.map_congr_left (λ arg _ ↦ (Arg.ground_eq arg σ).symm)

-- Finite superset of every atom that could ever be derived while
-- evaluating `p`: every atom occurring (as a head or body atom of some
-- rule) in `p`, grounded in every possible way using only constants that
-- already occur somewhere in `p`.
def Program.herbrand_base (p: Program): List GrAtom :=
  p.atoms.flatMap (Atom.groundings · p.consts)

-- The base introduces no new constants: a grounded argument is either one
-- of the `p.consts` substituted in, or a constant already written in the
-- source atom — and that atom's constants are `p.consts` by construction.
theorem Program.consts_of_mem_herbrand_base {p: Program} {a: GrAtom}:
    a ∈ p.herbrand_base →
    ∀ c ∈ a.val.consts, c ∈ p.consts
:= by
  intro ha c hc
  obtain ⟨b, hb, hab⟩ := List.mem_flatMap.mp ha
  obtain ⟨consts, hargs, rfl⟩ := List.mem_map.mp hab
  obtain ⟨c', hc', heq⟩ := List.mem_map.mp (Atom.mem_consts.mp hc)
  obtain ⟨x, hx, hcx⟩ := List.mem_choices_mem hargs _ (Sum.inr.inj heq ▸ hc')
  cases x with
  | inl v => exact hcx
  | inr c'' =>
    cases hcx with
    | head _ => exact List.mem_flatMap.mpr ⟨b, hb, Atom.mem_consts.mpr hx⟩
    | tail _ h => cases h
