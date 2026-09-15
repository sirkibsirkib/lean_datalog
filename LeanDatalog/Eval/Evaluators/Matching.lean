import LeanDatalog.Eval.Step
import LeanDatalog.Eval.Interface

/-
Saturation by backtracking search instead of enumeration.

`Program.stepAtoms` (Step.lean) tries every assignment of `p.consts` to a
rule's variables and keeps the ones whose body atoms already sit in `kb` —
`C^V` work per rule regardless of what `kb` contains. This module computes
the same immediate consequences a different way: walk a rule's body left to
right, and at each atom try it against every element of `kb` in turn,
growing a partial variable assignment and backtracking the instant two
atoms disagree about what a variable is worth.

The partial assignment is `Variable → Option Constant`, but realised as a
finite assoc list (`PartialSubst`) rather than a genuine function, so that
it can be built one entry at a time and inspected by structural recursion —
`none` for a variable is simply "no entry", exactly as `Subst.ofAssoc`
already reads such a list.
-/

-- A ground atom's `args` are all `.inr`, so `consts` (which just drops the
-- `.inl` case) recovers them exactly, in order.
theorem args_eq_consts_map_inr_aux:
  ∀ {args: List Arg}, args.all Groundable.grounded = true →
    args = (args.filterMap (λ | (.inl _: Arg) => none | .inr c => some c)).map Sum.inr
  | [], _ => rfl
  | .inl _ :: _, h => by simp [Groundable.grounded] at h
  | .inr c :: args, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := args_eq_consts_map_inr_aux h.2
    simp only [List.filterMap_cons, List.map_cons]
    rw [← ih]

theorem Atom.args_eq_consts_map_inr {a: Atom} (h: Groundable.grounded a):
    a.args = a.consts.map Sum.inr
:= args_eq_consts_map_inr_aux h

-- The other direction, needed for completeness: grounding `a` by `σ` and
-- then reading off its `consts` recovers exactly what grounding each
-- argument individually would have given.
theorem filterMap_ground_aux {σ: Subst}:
  ∀ {args: List Arg},
    (args.map (λ arg ↦ Subst.ground arg σ)).filterMap
        (λ | (.inl _: Arg) => none | .inr c => some c)
      = args.map (λ arg ↦ Arg.grounding arg σ)
  | [] => rfl
  | arg :: args => by
    simp only [List.map_cons]
    rw [Arg.ground_eq]
    simp only [List.filterMap_cons]
    rw [filterMap_ground_aux]

theorem Atom.consts_grounded {a: Atom} {σ: Subst}:
    (Subst.grounded a σ).val.consts = a.args.map (λ arg ↦ Arg.grounding arg σ)
:= filterMap_ground_aux

namespace Matching

abbrev PartialSubst := List (Variable × Constant)

def PartialSubst.lookup (ps: PartialSubst) (v: Variable): Option Constant :=
  (ps.find? (λ pr ↦ pr.1 == v)).map Prod.snd

-- The invariant a well-behaved partial substitution keeps: at most one
-- value on file per variable. `matchArg` below only ever adds an entry for
-- a variable that `lookup` just reported absent, which is what keeps this
-- true of everything the algorithm builds.
def PartialSubst.Functional (ps: PartialSubst): Prop :=
  ∀ v c c', (v, c) ∈ ps → (v, c') ∈ ps → c = c'

theorem PartialSubst.functional_nil: PartialSubst.Functional [] :=
  λ _ _ _ h _ ↦ nomatch h

-- Try one argument of a rule's atom against the constant sitting in the
-- matching position of a ground atom: a constant argument must equal it
-- outright, a variable already on file must agree with it, and an unseen
-- variable gets bound to it.
def matchArg (ps: PartialSubst) (pat: Arg) (val: Constant): Option PartialSubst :=
  match pat with
  | .inr c => if c = val then some ps else none
  | .inl v =>
    match ps.lookup v with
    | some c => if c = val then some ps else none
    | none => some ((v, val) :: ps)

-- Match every argument of a body atom against the corresponding constants
-- of a candidate ground atom, threading the partial substitution through
-- left to right. Arity mismatch (which the type system does not rule out —
-- two atoms may share a predicate symbol yet disagree on arity) fails
-- rather than matching a ragged prefix.
def matchArgs (ps: PartialSubst): List Arg → List Constant → Option PartialSubst
  | [], [] => some ps
  | pat :: pats, val :: vals =>
    (matchArg ps pat val).bind λ ps' ↦ matchArgs ps' pats vals
  | [], _ :: _ => none
  | _ :: _, [] => none

def matchAtom (ps: PartialSubst) (a: Atom) (g: GrAtom): Option PartialSubst :=
  if a.pred = g.val.pred then matchArgs ps a.args g.val.consts else none

-- The recursive walk over a rule's antecedents: for each body atom in
-- turn, try every element already in the knowledge base, keeping only the
-- combinations that match all the way to the end. `List.flatMap` is the
-- backtracking — a `none` from `matchAtom` contributes no continuations for
-- that choice of `g`, and every other choice of `g` is still tried.
def matchBody (kb: List GrAtom) (ps: PartialSubst):
    List Atom → List PartialSubst
  | [] => [ps]
  | a :: rest =>
    kb.flatMap λ g ↦
      match matchAtom ps a g with
      | some ps' => matchBody kb ps' rest
      | none => []

theorem PartialSubst.lookup_mem {ps: PartialSubst} {v: Variable} {c: Constant}:
    ps.lookup v = some c → (v, c) ∈ ps
:= by
  unfold PartialSubst.lookup
  intro h
  cases hfind: ps.find? (λ pr ↦ pr.1 == v) with
  | none => rw [hfind] at h; simp at h
  | some pr =>
    rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hp := List.find?_some hfind
    obtain ⟨v', c'⟩ := pr
    simp only [beq_iff_eq] at hp
    subst hp
    simp only at h
    subst h
    exact List.mem_of_find?_eq_some hfind

theorem PartialSubst.ofAssoc_of_mem {ps: PartialSubst} {v: Variable} {c: Constant}
    (hfunc: ps.Functional) (hmem: (v, c) ∈ ps):
    Subst.ofAssoc ps v = c
:= by
  obtain ⟨pr, hpr, hpr1, heq⟩ := Subst.ofAssoc_spec (l := ps) ⟨(v, c), hmem, rfl⟩
  obtain ⟨v', c'⟩ := pr
  simp only at hpr1
  rw [heq]
  exact (hfunc v c c' hmem (hpr1 ▸ hpr)).symm

theorem PartialSubst.lookup_eq_none {ps: PartialSubst} {v: Variable}
    (h: ps.lookup v = none):
    ∀ c, (v, c) ∉ ps
:= by
  unfold PartialSubst.lookup at h
  have hfind0: ps.find? (λ pr ↦ pr.1 == v) = none := by
    cases hf: ps.find? (λ pr ↦ pr.1 == v) with
    | none => rfl
    | some _ => rw [hf] at h; simp at h
  intro c hmem
  exact absurd (List.find?_eq_none.mp hfind0 (v, c) hmem) (by simp)

-- What `matchArg` returning `some ps'` amounts to, spelled out as a
-- disjunction of the three ways it can succeed — restating the definition
-- so every downstream fact about `matchArg` is a `rcases` away, with no
-- further need to re-unfold it.
theorem matchArg_cases {ps: PartialSubst} {pat: Arg} {val: Constant} {ps': PartialSubst}
    (heq: matchArg ps pat val = some ps'):
    (∃ c, pat = .inr c ∧ c = val ∧ ps' = ps)
  ∨ (∃ v c, pat = .inl v ∧ ps.lookup v = some c ∧ c = val ∧ ps' = ps)
  ∨ (∃ v, pat = .inl v ∧ ps.lookup v = none ∧ ps' = (v, val) :: ps)
:= by
  cases pat with
  | inr c =>
    simp only [matchArg] at heq
    by_cases hc: c = val
    · rw [if_pos hc] at heq
      exact .inl ⟨c, rfl, hc, (Option.some.inj heq).symm⟩
    · rw [if_neg hc] at heq
      cases heq
  | inl v =>
    simp only [matchArg] at heq
    cases hlook: ps.lookup v with
    | some c =>
      simp only [hlook] at heq
      by_cases hc: c = val
      · rw [if_pos hc] at heq
        exact .inr (.inl ⟨v, c, rfl, hlook, hc, (Option.some.inj heq).symm⟩)
      · rw [if_neg hc] at heq
        cases heq
    | none =>
      simp only [hlook] at heq
      exact .inr (.inr ⟨v, rfl, hlook, (Option.some.inj heq).symm⟩)

-- `matchArg` never disturbs an existing binding, so functionality survives
-- it: either it leaves `ps` untouched, or it adds a binding for a variable
-- `lookup` just reported absent — and an absent variable cannot already
-- clash with anything in `ps`.
theorem matchArg_functional {ps ps': PartialSubst} {pat: Arg} {val: Constant}
    (hfunc: ps.Functional) (heq: matchArg ps pat val = some ps'):
    ps'.Functional
:= by
  rcases matchArg_cases heq with ⟨c, hpat, hc, rfl⟩ | ⟨v, c, hpat, hlook, hc, rfl⟩ | ⟨v, hpat, hlook, rfl⟩
  · exact hfunc
  · exact hfunc
  · intro v₁ c₁ c₂ h₁ h₂
    cases h₁ with
    | head _ =>
      cases h₂ with
      | head _ => rfl
      | tail _ h₂ => exact absurd h₂ (PartialSubst.lookup_eq_none hlook c₂)
    | tail _ h₁ =>
      cases h₂ with
      | head _ => exact absurd h₁ (PartialSubst.lookup_eq_none hlook c₁)
      | tail _ h₂ => exact hfunc v₁ c₁ c₂ h₁ h₂

-- `matchArg` only ever grows `ps`.
theorem matchArg_subset {ps ps': PartialSubst} {pat: Arg} {val: Constant}
    (heq: matchArg ps pat val = some ps'):
    ∀ v c, (v, c) ∈ ps → (v, c) ∈ ps'
:= by
  rcases matchArg_cases heq with ⟨c, hpat, hc, rfl⟩ | ⟨v, c, hpat, hlook, hc, rfl⟩ | ⟨v, hpat, hlook, rfl⟩
  · exact λ _ _ h ↦ h
  · exact λ _ _ h ↦ h
  · exact λ _ _ h ↦ .tail _ h

-- What success actually pins down: a constant pattern equals `val`, and a
-- variable pattern ends up bound to `val` in the result.
theorem matchArg_mem {ps ps': PartialSubst} {pat: Arg} {val: Constant}
    (heq: matchArg ps pat val = some ps'):
    (∀ v, pat = .inl v → (v, val) ∈ ps') ∧ (∀ c, pat = .inr c → c = val)
:= by
  rcases matchArg_cases heq with ⟨c, hpat, hc, rfl⟩ | ⟨v, c, hpat, hlook, hc, rfl⟩ | ⟨v, hpat, hlook, rfl⟩
  · constructor
    · intro v' h; rw [hpat] at h; nomatch h
    · intro c' h; rw [hpat] at h; cases h; exact hc
  · constructor
    · intro v' h; rw [hpat] at h; cases h; rw [← hc]; exact PartialSubst.lookup_mem hlook
    · intro c' h; rw [hpat] at h; nomatch h
  · constructor
    · intro v' h; rw [hpat] at h; cases h; exact .head _
    · intro c' h; rw [hpat] at h; nomatch h

-- Completeness, argument by argument: matching `pat` against exactly the
-- value it would ground to under `σ` never backtracks — either `pat`
-- already agrees (constant, or a variable already on file per `hcompat`),
-- or it is an unseen variable and gets bound to precisely that value.
theorem matchArg_succeeds {ps: PartialSubst} {pat: Arg} {σ: Subst}
    (hcompat: ∀ v c, (v, c) ∈ ps → σ v = c):
    ∃ ps', matchArg ps pat (Arg.grounding pat σ) = some ps'
:= by
  cases pat with
  | inr c => exact ⟨ps, by simp [matchArg, Arg.grounding]⟩
  | inl v =>
    cases hlook: ps.lookup v with
    | some c =>
      have hcv := hcompat v c (PartialSubst.lookup_mem hlook)
      exact ⟨ps, by simp [matchArg, Arg.grounding, hlook, hcv]⟩
    | none => exact ⟨(v, σ v) :: ps, by simp [matchArg, Arg.grounding, hlook]⟩

-- ...and whatever it lands on is still compatible with `σ`, since the only
-- thing it can have added is `pat` bound to `pat`'s own value under `σ`.
theorem matchArg_compat {ps ps': PartialSubst} {pat: Arg} {σ: Subst} {val: Constant}
    (hcompat: ∀ v c, (v, c) ∈ ps → σ v = c)
    (hval: val = Arg.grounding pat σ)
    (heq: matchArg ps pat val = some ps'):
    ∀ v c, (v, c) ∈ ps' → σ v = c
:= by
  rcases matchArg_cases heq with ⟨c, hpat, hc, rfl⟩ | ⟨v, c, hpat, hlook, hc, rfl⟩ | ⟨v, hpat, hlook, rfl⟩
  · exact hcompat
  · exact hcompat
  · intro v₁ c₁ h
    cases h with
    | head _ => simp only [hpat, Arg.grounding] at hval; exact hval.symm
    | tail _ h => exact hcompat v₁ c₁ h

-- Lift `matchArg_functional` across a whole argument list.
theorem matchArgs_functional:
  ∀ {pats: List Arg} {vals: List Constant} {ps ps': PartialSubst},
    ps.Functional →
    matchArgs ps pats vals = some ps' →
    ps'.Functional
:= by
  intro pats
  induction pats with
  | nil =>
    intro vals ps ps' hfunc heq
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq; exact hfunc
    | cons _ _ => simp only [matchArgs] at heq; cases heq
  | cons pat pats ih =>
    intro vals ps ps' hfunc heq
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq
    | cons val vals =>
      simp only [matchArgs, Option.bind_eq_some_iff] at heq
      obtain ⟨ps₁, hm, hrest⟩ := heq
      exact ih (matchArg_functional hfunc hm) hrest

-- Lift `matchArg_subset` across a whole argument list.
theorem matchArgs_subset:
  ∀ {pats: List Arg} {vals: List Constant} {ps ps': PartialSubst},
    matchArgs ps pats vals = some ps' →
    ∀ v c, (v, c) ∈ ps → (v, c) ∈ ps'
:= by
  intro pats
  induction pats with
  | nil =>
    intro vals ps ps' heq
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq; exact λ _ _ h ↦ h
    | cons _ _ => simp only [matchArgs] at heq; cases heq
  | cons pat pats ih =>
    intro vals ps ps' heq
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq
    | cons val vals =>
      simp only [matchArgs, Option.bind_eq_some_iff] at heq
      obtain ⟨ps₁, hm, hrest⟩ := heq
      exact λ v c h ↦ ih hrest v c (matchArg_subset hm v c h)

-- Every variable occurring among the patterns ends up bound in the result.
theorem matchArgs_vars_mem:
  ∀ {pats: List Arg} {vals: List Constant} {ps ps': PartialSubst},
    matchArgs ps pats vals = some ps' →
    ∀ v, (Sum.inl v: Arg) ∈ pats → ∃ c, (v, c) ∈ ps'
:= by
  intro pats
  induction pats with
  | nil => intro vals ps ps' _ v hv; nomatch hv
  | cons pat pats ih =>
    intro vals ps ps' heq v hv
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq
    | cons val vals =>
      simp only [matchArgs, Option.bind_eq_some_iff] at heq
      obtain ⟨ps₁, hm, hrest⟩ := heq
      cases hv with
      | head _ =>
        obtain ⟨hmemv, _⟩ := matchArg_mem hm
        exact ⟨val, matchArgs_subset hrest v val (hmemv v rfl)⟩
      | tail _ hv => exact ih hrest v hv

-- The payoff: grounding the whole pattern list by the FINAL substitution
-- recovers `vals` exactly. Repeated variables are handled for free, since
-- the conclusion is one equation about one substitution rather than a
-- membership fact per occurrence.
theorem matchArgs_grounds:
  ∀ {pats: List Arg} {vals: List Constant} {ps ps': PartialSubst},
    ps.Functional →
    matchArgs ps pats vals = some ps' →
    pats.map (λ pat ↦ Arg.grounding pat (Subst.ofAssoc ps')) = vals
:= by
  intro pats
  induction pats with
  | nil =>
    intro vals ps ps' _ heq
    cases vals with
    | nil => rfl
    | cons _ _ => simp only [matchArgs] at heq; cases heq
  | cons pat pats ih =>
    intro vals ps ps' hfunc heq
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq
    | cons val vals =>
      simp only [matchArgs, Option.bind_eq_some_iff] at heq
      obtain ⟨ps₁, hm, hrest⟩ := heq
      have hfunc₁ := matchArg_functional hfunc hm
      have hfunc' := matchArgs_functional hfunc₁ hrest
      have hgr := ih hfunc₁ hrest
      have hval: Arg.grounding pat (Subst.ofAssoc ps') = val := by
        obtain ⟨hvarcase, hconstcase⟩ := matchArg_mem hm
        cases pat with
        | inr c =>
          have hcv := hconstcase c rfl
          simp only [Arg.grounding, hcv]
        | inl v =>
          have hmem := matchArgs_subset hrest v val (hvarcase v rfl)
          simp only [Arg.grounding]
          exact PartialSubst.ofAssoc_of_mem hfunc' hmem
      simp only [List.map_cons, hval, hgr]

-- Completeness, lifted across a whole argument list: matching against
-- exactly the values `σ` grounds them to always succeeds, and the result
-- stays compatible with `σ`. (Subset-growth and "every variable gets
-- bound" are already available from `matchArgs_subset`/`matchArgs_vars_mem`
-- once a witness like this one is in hand, so there is no need to
-- reprove them here.)
theorem matchArgs_succeeds {ps: PartialSubst} {σ: Subst}:
  ∀ {pats: List Arg},
    (∀ v c, (v, c) ∈ ps → σ v = c) →
    ∃ ps', matchArgs ps pats (pats.map (λ pat ↦ Arg.grounding pat σ)) = some ps'
    ∧ (∀ v c, (v, c) ∈ ps' → σ v = c)
:= by
  intro pats
  induction pats generalizing ps with
  | nil => intro hcompat; exact ⟨ps, rfl, hcompat⟩
  | cons pat pats ih =>
    intro hcompat
    obtain ⟨ps₁, hm⟩ := matchArg_succeeds (pat := pat) hcompat
    have hcompat₁ := matchArg_compat hcompat rfl hm
    obtain ⟨ps', hrest, hcompat'⟩ := ih hcompat₁
    refine ⟨ps', ?_, hcompat'⟩
    simp only [List.map_cons, matchArgs, Option.bind_eq_some_iff]
    exact ⟨ps₁, hm, hrest⟩

theorem matchAtom_functional {ps ps': PartialSubst} {a: Atom} {g: GrAtom}
    (hfunc: ps.Functional) (heq: matchAtom ps a g = some ps'):
    ps'.Functional
:= by
  simp only [matchAtom] at heq
  by_cases hpred: a.pred = g.val.pred
  · rw [if_pos hpred] at heq; exact matchArgs_functional hfunc heq
  · rw [if_neg hpred] at heq; cases heq

theorem matchAtom_subset {ps ps': PartialSubst} {a: Atom} {g: GrAtom}
    (heq: matchAtom ps a g = some ps'):
    ∀ v c, (v, c) ∈ ps → (v, c) ∈ ps'
:= by
  simp only [matchAtom] at heq
  by_cases hpred: a.pred = g.val.pred
  · rw [if_pos hpred] at heq; exact matchArgs_subset heq
  · rw [if_neg hpred] at heq; cases heq

theorem matchAtom_vars_mem {ps ps': PartialSubst} {a: Atom} {g: GrAtom}
    (heq: matchAtom ps a g = some ps'):
    ∀ v ∈ a.vars, ∃ c, (v, c) ∈ ps'
:= by
  simp only [matchAtom] at heq
  by_cases hpred: a.pred = g.val.pred
  · rw [if_pos hpred] at heq
    intro v hv
    exact matchArgs_vars_mem heq v (Atom.mem_vars.mp hv)
  · rw [if_neg hpred] at heq; cases heq

-- The core soundness fact about matching one atom: success grounds `a`
-- into exactly `g`, not merely into something with the right constants at
-- the right positions. Combines `matchArgs_grounds` (pointwise agreement)
-- with `Atom.args_eq_consts_map_inr` (a ground atom's `args` really are
-- `consts` reinjected), then closes by structure eta on `Atom`.
theorem matchAtom_grounds {ps ps': PartialSubst} {a: Atom} {g: GrAtom}
    (hfunc: ps.Functional) (heq: matchAtom ps a g = some ps'):
    Subst.grounded a (Subst.ofAssoc ps') = g
:= by
  simp only [matchAtom] at heq
  by_cases hpred: a.pred = g.val.pred
  · rw [if_pos hpred] at heq
    have hgr := matchArgs_grounds hfunc heq
    apply Subtype.ext
    show ({ pred := a.pred, args := a.args.map (λ arg ↦ Subst.ground arg (Subst.ofAssoc ps')) }: Atom)
        = g.val
    have hargseq: a.args.map (λ arg ↦ Subst.ground arg (Subst.ofAssoc ps'))
        = g.val.consts.map Sum.inr := by
      rw [← hgr, List.map_map]
      exact List.map_congr_left (λ arg _ ↦ Arg.ground_eq arg (Subst.ofAssoc ps'))
    rw [hargseq, ← Atom.args_eq_consts_map_inr g.2, hpred]
  · rw [if_neg hpred] at heq; cases heq

-- Completeness at the atom level: matching `a` against its own image under
-- `σ` always succeeds. `Atom.consts_grounded` is what lets `matchArgs_succeeds`
-- (stated in terms of `.map (grounding · σ)`) answer a question stated in
-- terms of `(Subst.grounded a σ).val.consts`.
theorem matchAtom_complete {ps: PartialSubst} {a: Atom} {σ: Subst}
    (hcompat: ∀ v c, (v, c) ∈ ps → σ v = c):
    ∃ ps', matchAtom ps a (Subst.grounded a σ) = some ps'
    ∧ (∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
    ∧ (∀ v c, (v, c) ∈ ps' → σ v = c)
:= by
  obtain ⟨ps', hm, hcompat'⟩ := matchArgs_succeeds (ps := ps) (σ := σ) (pats := a.args) hcompat
  have hma: matchAtom ps a (Subst.grounded a σ) = some ps' := by
    have hpred: a.pred = (Subst.grounded a σ).val.pred := rfl
    simp only [matchAtom]
    rw [if_pos hpred, Atom.consts_grounded]
    exact hm
  exact ⟨ps', hma, matchArgs_subset hm, hcompat'⟩

end Matching

-- Once every variable of `b` is genuinely on file in `ps` (not merely
-- defaulted), growing `ps` further along a functional extension cannot
-- change how `b` grounds: `Atom.ground_congr` needs only that the two
-- substitutions agree on `b`'s variables, and `PartialSubst.ofAssoc_of_mem`
-- reads the same value off either list.
theorem Atom.grounded_stable {b: Atom} {ps ps': Matching.PartialSubst} {g: GrAtom}
    (hpsf: ps.Functional) (hpsf': ps'.Functional)
    (hvars: ∀ v ∈ b.vars, ∃ c, (v, c) ∈ ps)
    (hsub: ∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
    (heq: Subst.grounded b (Subst.ofAssoc ps) = g):
    Subst.grounded b (Subst.ofAssoc ps') = g
:= by
  have hcongr: Subst.grounded b (Subst.ofAssoc ps') = Subst.grounded b (Subst.ofAssoc ps) := by
    apply Subtype.ext
    apply Atom.ground_congr
    intro v hv
    obtain ⟨c, hc⟩ := hvars v hv
    rw [Matching.PartialSubst.ofAssoc_of_mem hpsf' (hsub v c hc),
        Matching.PartialSubst.ofAssoc_of_mem hpsf hc]
  rw [hcongr, heq]

namespace Matching

-- Soundness of the whole backtracking walk: whatever partial substitution
-- it settles on is functional, extends the one it started from, and
-- grounds every antecedent it walked into something already in `kb`.
theorem matchBody_sound {kb: List GrAtom}:
  ∀ {body: List Atom} {ps ps': PartialSubst},
    ps.Functional →
    ps' ∈ matchBody kb ps body →
    ps'.Functional
  ∧ (∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
  ∧ (∀ b ∈ body, Subst.grounded b (Subst.ofAssoc ps') ∈ kb)
:= by
  intro body
  induction body with
  | nil =>
    intro ps ps' hfunc hmem
    simp only [matchBody, List.mem_singleton] at hmem
    subst hmem
    exact ⟨hfunc, λ _ _ h ↦ h, λ b hb ↦ nomatch hb⟩
  | cons b rest ih =>
    intro ps ps' hfunc hmem
    simp only [matchBody, List.mem_flatMap] at hmem
    obtain ⟨g, hg, hmem⟩ := hmem
    cases hma: matchAtom ps b g with
    | none => rw [hma] at hmem; nomatch hmem
    | some ps₁ =>
      rw [hma] at hmem
      have hfunc₁ := matchAtom_functional hfunc hma
      obtain ⟨hfunc', hsub', hbodyrest⟩ := ih hfunc₁ hmem
      have hsub := matchAtom_subset hma
      refine ⟨hfunc', λ v c h ↦ hsub' v c (hsub v c h), λ b' hb' ↦ ?_⟩
      cases hb' with
      | head _ =>
        have hg1 := matchAtom_grounds hfunc hma
        have hvars := matchAtom_vars_mem hma
        rw [Atom.grounded_stable hfunc₁ hfunc' hvars hsub' hg1]
        exact hg
      | tail _ hb' => exact hbodyrest b' hb'

-- Plain monotonicity of the walk, with no functionality needed: whatever
-- was on file when it started is still on file wherever it ends up.
theorem matchBody_subset {kb: List GrAtom}:
  ∀ {body: List Atom} {ps ps': PartialSubst},
    ps' ∈ matchBody kb ps body →
    ∀ v c, (v, c) ∈ ps → (v, c) ∈ ps'
:= by
  intro body
  induction body with
  | nil =>
    intro ps ps' hmem
    simp only [matchBody, List.mem_singleton] at hmem
    subst hmem
    exact λ _ _ h ↦ h
  | cons b rest ih =>
    intro ps ps' hmem
    simp only [matchBody, List.mem_flatMap] at hmem
    obtain ⟨g, hg, hmem⟩ := hmem
    cases hma: matchAtom ps b g with
    | none => simp only [hma] at hmem; nomatch hmem
    | some ps₁ =>
      simp only [hma] at hmem
      exact λ v c h ↦ ih hmem v c (matchAtom_subset hma v c h)

-- Every variable of every antecedent the walk got past ends up bound.
theorem matchBody_vars_mem {kb: List GrAtom}:
  ∀ {body: List Atom} {ps ps': PartialSubst},
    ps' ∈ matchBody kb ps body →
    ∀ b ∈ body, ∀ v ∈ b.vars, ∃ c, (v, c) ∈ ps'
:= by
  intro body
  induction body with
  | nil => intro ps ps' _ b hb; nomatch hb
  | cons b rest ih =>
    intro ps ps' hmem b' hb' v hv
    simp only [matchBody, List.mem_flatMap] at hmem
    obtain ⟨g, hg, hmem⟩ := hmem
    cases hma: matchAtom ps b g with
    | none => simp only [hma] at hmem; nomatch hmem
    | some ps₁ =>
      simp only [hma] at hmem
      cases hb' with
      | head _ =>
        obtain ⟨c, hc⟩ := matchAtom_vars_mem hma v hv
        exact ⟨c, matchBody_subset hmem v c hc⟩
      | tail _ hb' => exact ih hmem b' hb' v hv

-- Completeness of the whole walk: if `σ` fires the body against `kb`, the
-- walk finds SOME partial substitution — not necessarily `σ` itself, but
-- one that agrees with `σ` everywhere it is defined, which is exactly what
-- `matchBody_vars_mem` + `hcompat` need to reconstruct `σ`'s ground
-- instance of anything built from this body's variables.
theorem matchBody_complete {kb: List GrAtom} {σ: Subst}:
  ∀ {body: List Atom} {ps: PartialSubst},
    ps.Functional →
    (∀ v c, (v, c) ∈ ps → σ v = c) →
    (∀ b ∈ body, Subst.grounded b σ ∈ kb) →
    ∃ ps' ∈ matchBody kb ps body,
      (∀ v c, (v, c) ∈ ps' → σ v = c)
:= by
  intro body
  induction body with
  | nil =>
    intro ps hfunc hcompat _
    exact ⟨ps, .head _, hcompat⟩
  | cons b rest ih =>
    intro ps hfunc hcompat hbodykb
    have hgkb: Subst.grounded b σ ∈ kb := hbodykb b (.head _)
    obtain ⟨ps₁, hma, _, hcompat₁⟩ := matchAtom_complete (a := b) hcompat
    have hfunc₁ := matchAtom_functional hfunc hma
    obtain ⟨ps', hmem', hcompat'⟩ :=
      ih hfunc₁ hcompat₁ (λ b' hb' ↦ hbodykb b' (.tail _ hb'))
    refine ⟨ps', ?_, hcompat'⟩
    simp only [matchBody, List.mem_flatMap]
    refine ⟨Subst.grounded b σ, hgkb, ?_⟩
    simp only [hma]
    exact hmem'

end Matching

-- Trimmed to the Herbrand base up front, by an explicit filter. Without
-- this, membership in `matchStepAtoms p kb` would only land in the base
-- when `kb` itself already does (unlike Step.lean's candidate
-- substitutions, which get that confinement for free from `p.consts`
-- regardless of `kb` — matching draws its values straight out of `kb`).
-- Filtering here keeps that invariant unconditional, so `saturateGo` below
-- can be the same one-tick-per-atom loop as Stepwise.lean's, with no extra
-- bookkeeping threaded through its well-founded recursion.
def Program.matchStepAtoms (p: Program) (kb: List GrAtom): List GrAtom :=
  (p.flatMap λ r ↦
    (Matching.matchBody kb [] r.body).map λ ps ↦ Subst.grounded r.head (Subst.ofAssoc ps))
  |>.filter (λ a ↦ decide (a ∈ p.herbrand_base))

-- Soundness, in the same shape as `Program.mem_stepAtoms` (Step.lean): every
-- atom the matcher produces is some rule's head under a substitution whose
-- body fires against `kb`.
theorem Program.mem_matchStepAtoms {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.matchStepAtoms kb →
    ∃ r ∈ p, ∃ σ: Subst,
      (∀ b ∈ r.body, Subst.grounded b σ ∈ kb)
    ∧ a = Subst.grounded r.head σ
:= by
  intro ha
  unfold Program.matchStepAtoms at ha
  obtain ⟨ha, _⟩ := List.mem_filter.mp ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨ps, hps, rfl⟩ := List.mem_map.mp ha
  obtain ⟨_, _, hbody⟩ := Matching.matchBody_sound Matching.PartialSubst.functional_nil hps
  exact ⟨r, hr, Subst.ofAssoc ps, hbody, rfl⟩

-- ...and, by construction of the filter, unconditionally in the base —
-- with no need for `kb` itself to be bounded first.
theorem Program.matchStepAtoms_mem_herbrand_base {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.matchStepAtoms kb →
    a ∈ p.herbrand_base
:= by
  intro ha
  unfold Program.matchStepAtoms at ha
  exact (of_decide_eq_true (List.mem_filter.mp ha).2)

-- COMPLETENESS: if any substitution fires a rule against `kb`, the walk
-- already produces that head — the payoff of matching rather than blind
-- enumeration. `matchBody_complete` supplies a partial substitution
-- agreeing with `σ` wherever it is defined; `matchBody_vars_mem` says that
-- covers every variable `r.head` could mention, by `Rule.safe`; and
-- `Atom.ground_congr` turns that pointwise agreement into equality of the
-- grounded heads. `hbound` is only needed to show the result survives the
-- filter, exactly as `Program.mem_stepAtoms_of_fires` needs it in Step.lean.
theorem Program.mem_matchStepAtoms_of_fires {p: Program} {r: Rule} {σ: Subst} {kb: List GrAtom}
    (hr: r ∈ p)
    (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base)
    (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    Subst.grounded r.head σ ∈ p.matchStepAtoms kb
:= by
  obtain ⟨ps', hmem', hcompat'⟩ :=
    Matching.matchBody_complete Matching.PartialSubst.functional_nil
      (λ v c h ↦ nomatch h) hbody
  obtain ⟨hfunc', _, _⟩ := Matching.matchBody_sound Matching.PartialSubst.functional_nil hmem'
  have heq: Subst.grounded r.head (Subst.ofAssoc ps') = Subst.grounded r.head σ := by
    apply Subtype.ext
    apply Atom.ground_congr
    intro v hv
    obtain ⟨b, hb, hbv⟩ := r.safe v hv
    obtain ⟨c, hc⟩ := Matching.matchBody_vars_mem hmem' b hb v hbv
    rw [Matching.PartialSubst.ofAssoc_of_mem hfunc' hc]
    exact (hcompat' v c hc).symm
  have hcs: ∀ v ∈ r.vars, σ v ∈ p.consts := Program.subst_consts hbound hbody
  have hbase: Subst.grounded r.head σ ∈ p.herbrand_base := by
    refine List.mem_flatMap.mpr ⟨r.head, List.mem_flatMap.mpr ⟨r, hr, .head _⟩, ?_⟩
    refine Atom.mem_groundings (λ v hv ↦ hcs v ?_)
    obtain ⟨b, hb, hbv⟩ := r.safe v hv
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hbv⟩)
  unfold Program.matchStepAtoms
  rw [← heq]
  refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨ps', hmem', rfl⟩⟩, ?_⟩
  rw [heq]
  exact decide_eq_true hbase

-- The program `p(a).  q(X) :- p(X).`, as in Step.lean.
private def X: Variable := ⟨"X", by decide⟩
private def a: Constant := ⟨"a", by decide⟩
private def p: Constant := ⟨"p", by decide⟩
private def q: Constant := ⟨"q", by decide⟩
private def prog: Program :=
  [ ⟨⟨p, [.inr a]⟩, []             , by decide⟩
  , ⟨⟨q, [.inl X]⟩, [⟨p, [.inl X]⟩], by decide⟩ ]
private def pa: GrAtom := ⟨⟨p, [.inr a]⟩, by decide⟩
private def qa: GrAtom := ⟨⟨q, [.inr a]⟩, by decide⟩

namespace Matching

-- Saturation itself: tick once per derived atom, exactly like
-- Stepwise.lean, just consuming `Program.matchStepAtoms` instead of
-- `Program.stepAtoms`. Filtering `matchStepAtoms` to the Herbrand base up
-- front (see its definition above) is what keeps this loop word-for-word
-- the same shape as Stepwise.lean's — no invariant needs threading through
-- the well-founded recursion itself.
def saturateGo (p: Program) (kb: List GrAtom): List GrAtom :=
  match _hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
  | none => kb
  | some a => saturateGo p (a :: kb)
termination_by p.herbrand_base.countP λ b ↦ decide (b ∉ kb)
decreasing_by
  have hmem := List.mem_of_find?_eq_some _hfind
  have hnew: a ∉ kb := by simpa using List.find?_some _hfind
  refine List.countP_lt_countP (a := a)
    ?_ (Program.matchStepAtoms_mem_herbrand_base hmem) ?_ ?_
  · intro x _ hx
    simp only [decide_eq_true_iff] at hx ⊢
    exact λ hg ↦ hx (.tail _ hg)
  · simpa using hnew
  · simp only [decide_eq_true_iff]
    exact λ h ↦ h (.head _)

def saturate (p: Program): List GrAtom :=
  saturateGo p []

-- The loop returns only at a fixpoint: `find?` yielding nothing means
-- every consequence of the knowledge base is already in it.
theorem saturateGo_fixpoint (p: Program):
  ∀ kb, ∀ a ∈ p.matchStepAtoms (saturateGo p kb), a ∈ saturateGo p kb
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hfind =>
    rw [saturateGo.eq_def, hfind]
    intro a ha
    simpa using List.find?_eq_none.mp hfind a ha
  | case2 kb a hfind ih =>
    rw [saturateGo.eq_def, hfind]
    exact ih

-- The Herbrand bound is an invariant of the loop.
theorem saturateGo_bounded (p: Program):
  ∀ kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    ∀ g ∈ saturateGo p kb, g ∈ p.herbrand_base
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hfind =>
    intro hb
    rw [saturateGo.eq_def, hfind]
    exact hb
  | case2 kb a hfind ih =>
    intro hb
    rw [saturateGo.eq_def, hfind]
    refine ih (λ g hg ↦ ?_)
    cases hg with
    | head _ => exact Program.matchStepAtoms_mem_herbrand_base (List.mem_of_find?_eq_some hfind)
    | tail _ hg => exact hb g hg

-- Each iteration is one `infer` step, so the result stays reachable.
theorem saturateGo_reachable (p: Program):
  ∀ kb, p.infer.ReflTransGen ∅ (λ g ↦ g ∈ kb) →
    p.infer.ReflTransGen ∅ (λ g ↦ g ∈ saturateGo p kb)
:= by
  intro kb
  induction kb using saturateGo.induct p with
  | case1 kb hfind =>
    intro h
    rw [saturateGo.eq_def, hfind]
    exact h
  | case2 kb a hfind ih =>
    intro h
    rw [saturateGo.eq_def, hfind]
    refine ih (.snoc _ _ _ h ?_)
    obtain ⟨r, hr, σ, hbody, rfl⟩ :=
      Program.mem_matchStepAtoms (List.mem_of_find?_eq_some hfind)
    have hnew := List.find?_some hfind
    simp only [decide_eq_true_iff] at hnew
    exact ⟨r, hr, σ, hbody, hnew, Set.ofList_cons⟩

theorem saturate_model (p: Program):
    p.model (· ∈ saturate p)
:= by
  have hbound := saturateGo_bounded p [] (λ g hg ↦ nomatch hg)
  constructor
  · refine saturateGo_reachable p [] ?_
    rw [Set.ofList_nil]
    exact .refl _
  · rintro ⟨kb', r, hr, σ, hfires, hnew, _⟩
    exact hnew (saturateGo_fixpoint p [] _
      (Program.mem_matchStepAtoms_of_fires hr hbound hfires))

def evaluator: Evaluator := ⟨saturate, saturate_model⟩

end Matching

example: prog.matchStepAtoms []   = [pa]     := by decide
example: prog.matchStepAtoms [pa] = [pa, qa] := by decide
