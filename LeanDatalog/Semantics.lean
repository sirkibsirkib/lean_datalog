import LeanDatalog.Ground
import LeanDatalog.Utils.Set
import LeanDatalog.Utils.Relation

/-
The declarative semantics of a Datalog program.

Everything here is a `Prop`: no `Option`, no `if`, nothing that computes.
That is what lets these definitions read like the textbook — a knowledge
base is a set of ground atoms, and inference adds one atom licensed by one
rule.

Staying in `Prop` costs nothing computationally, so there is no reason to
duplicate any of this in `Bool`. Each definition quantifies over a rule
body, which is a finite `List`, so `Rule.fires` is decidable for any
knowledge base whose membership is decidable — see the example at the
bottom, and the `Decidable (a ∈ s)` bridge in Set.lean. An evaluator can
reuse these definitions rather than restate them.
-/

-- What a program knows: a set of ground atoms.
abbrev Kb := Set GrAtom

-- `σ` grounds every atom of `r`'s body into something `kb` already knows.
def Rule.fires (r: Rule) (σ: Subst) (kb: Kb): Prop :=
  ∀ a ∈ r.body, σ.grounded a ∈ kb

-- One step of inference: some rule of `p`, grounded by some `σ`, has its
-- whole body in `kb`, so its head joins the knowledge base. The head has to
-- be new, or a `kb` could always step to itself and nothing would ever
-- count as a normal form.
def Program.infer (p: Program) (kb kb': Kb): Prop :=
  ∃ r ∈ p, ∃ σ: Subst,
    r.fires σ kb
  ∧ σ.grounded r.head ∉ kb
  ∧ kb' = kb ∪ {σ.grounded r.head}

-- `kb` is everything `p` derives starting from nothing, and nothing more:
-- a normal form of `infer`, reached from the empty knowledge base. "No rule
-- of `p` can add anything to `kb`" is exactly `Normal` at this relation, so
-- there is no separate notion of saturation worth naming.
def Program.model (p: Program) (kb: Kb): Prop :=
  p.infer.ReflTransGen ∅ kb
∧ p.infer.Normal kb

-- The hook the computational side will hang off: the spec above is already
-- decidable wherever the knowledge base's membership is, so evaluation can
-- test this very definition instead of a `Bool`-valued copy of it.
example (r: Rule) (σ: Subst) (kb: Kb) [DecidablePred kb]:
    Decidable (r.fires σ kb) := by
  unfold Rule.fires
  infer_instance

-- A knowledge base backed by a finite list supplies that instance for free.
example (l: List GrAtom) (r: Rule) (σ: Subst):
    Decidable (r.fires σ (· ∈ l)) := by
  unfold Rule.fires
  infer_instance
