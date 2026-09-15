import LeanDatalog.Utils.Relation.Closure

/-
Confluence: whether the order in which steps are taken can change where you
end up. Nothing here needs the relation to terminate.
-/

namespace Function

-- `x` and `y` can be driven back together by reducing each some number of
-- times. This is what "the order of steps didn't matter" means.
def Joinable {α: Type} (r: EndoRel α) (x y: α): Prop :=
  ∃ w, r.ReflTransGen x w ∧ r.ReflTransGen y w

-- Any two reduction sequences out of a common start can be reconciled, so
-- a normal form, if reached at all, is reached no matter how one proceeds.
--
--            x            ↙ ↘  any number of steps
--         ↙     ↘         ↘ ↙  any number of steps
--       y         z
--         ↘     ↙
--            w
def Confluent {α: Type} (r: EndoRel α): Prop :=
  ∀ x y z,
    r.ReflTransGen x y →
    r.ReflTransGen x z →
    r.Joinable y z

-- The same demand made only of SINGLE steps out of `x`. Much easier to
-- establish, and genuinely weaker: local confluence implies confluence
-- only in the presence of termination (Newman's lemma).
--
--            x            ↙ ↘  exactly one step
--         ↙     ↘         ↘ ↙  any number of steps
--       y         z
--         ↘     ↙
--            w
def LocallyConfluent {α: Type} (r: EndoRel α): Prop :=
  ∀ x y z,
    r x y →
    r x z →
    r.Joinable y z

theorem Confluent.locallyConfluent {α: Type} {r: EndoRel α}:
    r.Confluent →
    r.LocallyConfluent
:= λ h x y z hxy hxz ↦ h x y z (.single hxy) (.single hxz)

-- Any two single steps out of `x` close up again with AT MOST one step on
-- each side. Strictly stronger than `LocallyConfluent`, and unlike it,
-- enough to give `Confluent` outright — with no termination argument,
-- which matters for any relation not known to terminate.
--
--            x            ↙ ↘  exactly one step
--         ↙     ↘         ↘ ↙  at most one step
--       y         z
--         ↘     ↙       The bottom pair may be empty: when the two steps
--            w         already agreed, `y = z = w` and nothing is needed.
def SemiDiamond {α: Type} (r: EndoRel α): Prop :=
  ∀ x y z,
    r x y →
    r x z →
    ∃ w, r.ReflGen y w ∧ r.ReflGen z w

theorem SemiDiamond.locallyConfluent {α: Type} {r: EndoRel α}:
    r.SemiDiamond →
    r.LocallyConfluent
:= by
  intro hd x y z hxy hxz
  obtain ⟨w, hyw, hzw⟩ := hd x y z hxy hxz
  exact ⟨w, hyw.toReflTransGen, hzw.toReflTransGen⟩

-- Peel one step off the left of a whole reduction sequence. The `ReflGen`
-- on the right is what makes the induction go through: a plain step would
-- not survive, and a full sequence would beg the question.
theorem SemiDiamond.strip {α: Type} {r: EndoRel α} (hd: r.SemiDiamond):
  ∀ {x y z: α},
    r.ReflGen x y →
    r.ReflTransGen x z →
    ∃ w, r.ReflTransGen y w ∧ r.ReflGen z w
:= by
  intro x y z hxy hxz
  induction hxz with
  | refl _ => exact ⟨y, .refl _, hxy⟩
  | snoc _ z' z _ hz'z ih =>
    obtain ⟨w, hyw, hz'w⟩ := ih hxy
    cases hz'w with
    | refl _ => exact ⟨z, hyw.trans (.single hz'z), .refl _⟩
    | single _ _ hz'w =>
      obtain ⟨v, hwv, hzv⟩ := hd _ _ _ hz'w hz'z
      exact ⟨v, hyw.trans hwv.toReflTransGen, hzv⟩

theorem SemiDiamond.confluent {α: Type} {r: EndoRel α}:
    r.SemiDiamond →
    r.Confluent
:= by
  intro hd x y z hxy hxz
  induction hxy with
  | refl _ => exact ⟨z, hxz, .refl _⟩
  | snoc _ y' y _ hy'y ih =>
    obtain ⟨w, hy'w, hzw⟩ := ih hxz
    obtain ⟨v, hyv, hwv⟩ := hd.strip (.single _ _ hy'y) hy'w
    exact ⟨v, hyv, hzw.trans hwv.toReflTransGen⟩

end Function
