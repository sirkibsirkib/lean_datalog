import LeanDatalog.SemanticProps

/-
Enumerating candidate substitutions.

Rather than matching a rule body against the knowledge base, every
assignment of `p.consts` to a rule's variables is tried. That is sound
because `Rule.safe` puts every head variable in the body and
`Program.infer_mem_herbrand_base` confines every derivable constant to
`p.consts`, so the enumeration misses nothing — see
`Program.mem_stepAtoms_of_fires` in Step.lean. It is also why this is
costly: |consts| ^ |vars| per rule, independent of what is in the base.
-/

-- Any constant will do for variables an assignment says nothing about;
-- a rule only ever reads the variables it mentions.
instance: Inhabited Constant := ⟨"a", by decide⟩

-- Total-ise a finite assignment into a `Subst`.
def Subst.ofAssoc (l: List (Variable × Constant)): Subst :=
  λ v ↦ (l.find? λ p ↦ p.1 == v).elim default Prod.snd

-- The variables a rule's body mentions. By `Rule.safe` these include every
-- head variable, so a substitution's values here settle the whole ground
-- instance.
def Rule.vars (r: Rule): List Variable :=
  (r.body.flatMap Atom.vars).eraseDups

-- Every assignment of constants drawn from `cs` to `vs`, as assoc lists.
-- Enumerating the PAIRS rather than the values keeps each entry's variable
-- attached, which is what makes the two lemmas below fall out of the
-- `List.choices` lemmas already proved.
def Variable.assignments (vs: List Variable) (cs: List Constant):
    List (List (Variable × Constant)) :=
  List.choices (vs.map λ v ↦ cs.map (Prod.mk v))

-- Every value in an enumerated assignment came from `cs`.
theorem Variable.assignments_mem {vs: List Variable} {cs: List Constant}
    {l: List (Variable × Constant)}:
    l ∈ Variable.assignments vs cs →
    ∀ pr ∈ l, pr.2 ∈ cs
:= by
  intro hl pr hpr
  obtain ⟨v, _, hmem⟩ := List.mem_choices_mem hl pr hpr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
  exact hc

-- ...and an enumerated assignment assigns to exactly `vs`, in order.
theorem Variable.assignments_fst {cs: List Constant}:
  ∀ {vs: List Variable} {l: List (Variable × Constant)},
    l ∈ Variable.assignments vs cs →
    l.map Prod.fst = vs
:= by
  intro vs
  induction vs with
  | nil =>
    intro l hl
    simp only [Variable.assignments, List.map, List.choices, List.mem_singleton] at hl
    subst hl
    rfl
  | cons v vs ih =>
    intro l hl
    simp only [Variable.assignments, List.map, List.choices,
      List.mem_flatMap, List.mem_map] at hl
    obtain ⟨pr, hpr, l', hl', rfl⟩ := hl
    obtain ⟨c, _, rfl⟩ := hpr
    exact congrArg (v :: ·) (ih hl')

-- Any substitution whose values on `vs` lie in `cs` is enumerated.
theorem Variable.assignments_complete {vs: List Variable} {cs: List Constant}
    {σ: Subst}:
    (∀ v ∈ vs, σ v ∈ cs) →
    vs.map (λ v ↦ (v, σ v)) ∈ Variable.assignments vs cs
:= λ h ↦ List.map_mem_choices (λ v hv ↦ List.mem_map.mpr ⟨σ v, h v hv, rfl⟩)

-- `ofAssoc` finds a matching entry whenever one exists.
theorem Subst.ofAssoc_spec {l: List (Variable × Constant)} {v: Variable}:
    (∃ pr ∈ l, pr.1 = v) →
    ∃ pr ∈ l, pr.1 = v ∧ Subst.ofAssoc l v = pr.2
:= by
  intro hex
  unfold Subst.ofAssoc
  cases hfind: l.find? (λ p ↦ p.1 == v) with
  | none =>
    obtain ⟨pr, hpr, hpv⟩ := hex
    rw [List.find?_eq_none] at hfind
    exact absurd (by simp [hpv]) (hfind pr hpr)
  | some pr =>
    exact ⟨pr, List.mem_of_find?_eq_some hfind,
      Subtype.ext (by simpa using List.find?_some hfind), rfl⟩

-- A value looked up in an enumerated assignment came from `cs`. Together
-- with `Atom.mem_groundings` this is what keeps candidates inside the base.
theorem Subst.ofAssoc_mem_cs {vs: List Variable} {cs: List Constant}
    {l: List (Variable × Constant)} {v: Variable}:
    l ∈ Variable.assignments vs cs →
    v ∈ vs →
    Subst.ofAssoc l v ∈ cs
:= by
  intro hl hv
  obtain ⟨pr, hpr, hpv⟩ := List.mem_map.mp (Variable.assignments_fst hl ▸ hv)
  obtain ⟨pr', hpr', _, heq⟩ := Subst.ofAssoc_spec ⟨pr, hpr, hpv⟩
  rw [heq]
  exact Variable.assignments_mem hl pr' hpr'

-- The assignment read off a substitution looks that substitution back up.
theorem Subst.ofAssoc_map {vs: List Variable} {σ: Subst} {v: Variable}:
    v ∈ vs →
    Subst.ofAssoc (vs.map λ w ↦ (w, σ w)) v = σ v
:= by
  intro hv
  obtain ⟨pr, hpr, hpv, heq⟩ :=
    Subst.ofAssoc_spec (l := vs.map λ w ↦ (w, σ w))
      ⟨(v, σ v), List.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hpr
  simp only at hpv heq
  subst hpv
  exact heq

def Rule.candidateSubsts (r: Rule) (cs: List Constant): List Subst :=
  (Variable.assignments r.vars cs).map Subst.ofAssoc

-- Grounding depends only on the substitution's values at the atom's own
-- variables, so a candidate that agrees with `σ` on `r.vars` grounds `r`
-- exactly as `σ` does.
theorem Atom.ground_congr {a: Atom} {σ σ': Subst}:
    (∀ v ∈ a.vars, σ v = σ' v) →
    Subst.ground a σ = Subst.ground a σ'
:= by
  intro h
  show (⟨a.pred, _⟩: Atom) = ⟨a.pred, _⟩
  congr 1
  refine List.map_congr_left ?_
  intro arg harg
  cases arg with
  | inl v => exact congrArg Sum.inr (h v (Atom.mem_vars.mpr harg))
  | inr c => rfl

-- Every head derivable from `kb` in a single step. A rule with an empty
-- body fires unconditionally, and safety forces its head to be ground.
