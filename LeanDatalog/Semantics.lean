import LeanDatalog.Ground
import LeanDatalog.Utils.Set
import LeanDatalog.Utils.Relation

/-
The declarative semantics of a Datalog program.

Everything here is a `Prop`, so the definitions read like the textbook: a
knowledge base is a set of ground atoms, and inference adds one atom
licensed by one rule.

That costs nothing computationally. `Rule.fires` quantifies over a finite
body, so it is decidable whenever the knowledge base's membership is (see
the examples at the bottom), and evaluators need no `Bool` copy of it.
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

example (r: Rule) (σ: Subst) (kb: Kb) [DecidablePred kb]:
    Decidable (r.fires σ kb) := by
  unfold Rule.fires
  infer_instance

-- A knowledge base backed by a finite list supplies that instance for free.
example (l: List GrAtom) (r: Rule) (σ: Subst):
    Decidable (r.fires σ (· ∈ l)) := by
  unfold Rule.fires
  infer_instance
