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
atoms disagree about what a variable is worth. For `body = [p(X,Y), q(Y)]`
against `kb = {g₁, g₂, g₃}`, the search looks like:

           p(X,Y)                  — try every g ∈ kb for the first atom
        ╱    |    ╲
      g₁     g₂     g₃             — g₂ doesn't match p(X,Y): dead end
      │      ✗      │
    q(Y)           q(Y)            — continue each surviving branch
    ╱  ╲            |
   g₁   g₂          ✗              — no g matches q(Y) here either
   ✗    ✓
        │
       ps                          — the one binding that matched all the way

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

-- What one successful argument match pins down, all at once: functionality
-- survives it (either `ps` is untouched, or the one new binding cannot
-- clash — `lookup` just reported the variable absent), `ps` only grows, and
-- the pattern itself now agrees with `val`.
theorem matchArg_sound {ps ps': PartialSubst} {pat: Arg} {val: Constant}
    (hfunc: ps.Functional) (heq: matchArg ps pat val = some ps'):
    ps'.Functional
  ∧ (∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
  ∧ (∀ v, pat = .inl v → (v, val) ∈ ps')
  ∧ (∀ c, pat = .inr c → c = val)
:= by
  rcases matchArg_cases heq with ⟨c, hpat, hc, rfl⟩ | ⟨v, c, hpat, hlook, hc, rfl⟩ | ⟨v, hpat, hlook, rfl⟩
  · refine ⟨hfunc, λ _ _ h ↦ h, ?_, ?_⟩
    · intro v' h; rw [hpat] at h; nomatch h
    · intro c' h; rw [hpat] at h; cases h; exact hc
  · refine ⟨hfunc, λ _ _ h ↦ h, ?_, ?_⟩
    · intro v' h; rw [hpat] at h; cases h; rw [← hc]; exact PartialSubst.lookup_mem hlook
    · intro c' h; rw [hpat] at h; nomatch h
  · refine ⟨?_, λ _ _ h ↦ .tail _ h, ?_, ?_⟩
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

-- `matchArg_sound`, lifted across a whole argument list by one induction —
-- what were four separate lemmas (functionality, monotonicity, "every
-- variable gets bound", and the grounding equation) all fall out of the
-- same case split, so there is no reason to redo it four times.
theorem matchArgs_sound:
  ∀ {pats: List Arg} {vals: List Constant} {ps ps': PartialSubst},
    ps.Functional →
    matchArgs ps pats vals = some ps' →
    ps'.Functional
  ∧ (∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
  ∧ (∀ v, (Sum.inl v: Arg) ∈ pats → ∃ c, (v, c) ∈ ps')
  ∧ pats.map (λ pat ↦ Arg.grounding pat (Subst.ofAssoc ps')) = vals
:= by
  intro pats
  induction pats with
  | nil =>
    intro vals ps ps' hfunc heq
    cases vals with
    | nil =>
      simp only [matchArgs] at heq
      cases heq
      refine ⟨hfunc, λ _ _ h ↦ h, ?_, rfl⟩
      intro v hv
      nomatch hv
    | cons _ _ => simp only [matchArgs] at heq; cases heq
  | cons pat pats ih =>
    intro vals ps ps' hfunc heq
    cases vals with
    | nil => simp only [matchArgs] at heq; cases heq
    | cons val vals =>
      simp only [matchArgs, Option.bind_eq_some_iff] at heq
      obtain ⟨ps₁, hm, hrest⟩ := heq
      obtain ⟨hfunc₁, hsub₁, hmem₁, hconst₁⟩ := matchArg_sound hfunc hm
      obtain ⟨hfunc', hsub', hvars', hgr⟩ := ih hfunc₁ hrest
      refine ⟨hfunc', λ v c h ↦ hsub' v c (hsub₁ v c h), ?_, ?_⟩
      · intro v hv
        cases hv with
        | head _ => exact ⟨val, hsub' v val (hmem₁ v rfl)⟩
        | tail _ hv => exact hvars' v hv
      · have hval: Arg.grounding pat (Subst.ofAssoc ps') = val := by
          cases pat with
          | inr c => simp only [Arg.grounding, hconst₁ c rfl]
          | inl v =>
            simp only [Arg.grounding]
            exact PartialSubst.ofAssoc_of_mem hfunc' (hsub' v val (hmem₁ v rfl))
        simp only [List.map_cons, hval, hgr]

-- Completeness, lifted across a whole argument list: matching against
-- exactly the values `σ` grounds them to always succeeds, and the result
-- stays compatible with `σ`. (Monotonicity and "every variable gets bound"
-- are already available from `matchArgs_sound` once a witness like this
-- one is in hand, so there is no need to reprove them here.)
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

-- `matchArgs_sound`, lifted to a whole atom: matching `a` against `g`
-- either fails outright on mismatched predicates, or is exactly
-- `matchArgs` on `a`'s arguments against `g`'s constants — so this is
-- `matchArgs_sound` plus `Atom.args_eq_consts_map_inr` (a ground atom's
-- `args` really are its `consts` reinjected) closed by structure eta.
theorem matchAtom_sound {ps ps': PartialSubst} {a: Atom} {g: GrAtom}
    (hfunc: ps.Functional) (heq: matchAtom ps a g = some ps'):
    ps'.Functional
  ∧ (∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
  ∧ (∀ v ∈ a.vars, ∃ c, (v, c) ∈ ps')
  ∧ Subst.grounded a (Subst.ofAssoc ps') = g
:= by
  simp only [matchAtom] at heq
  by_cases hpred: a.pred = g.val.pred
  · rw [if_pos hpred] at heq
    obtain ⟨hfunc', hsub', hvars', hgr⟩ := matchArgs_sound hfunc heq
    refine ⟨hfunc', hsub', λ v hv ↦ hvars' v (Atom.mem_vars.mp hv), ?_⟩
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
    ∧ (∀ v c, (v, c) ∈ ps' → σ v = c)
:= by
  obtain ⟨ps', hm, hcompat'⟩ := matchArgs_succeeds (ps := ps) (σ := σ) (pats := a.args) hcompat
  have hma: matchAtom ps a (Subst.grounded a σ) = some ps' := by
    have hpred: a.pred = (Subst.grounded a σ).val.pred := rfl
    simp only [matchAtom]
    rw [if_pos hpred, Atom.consts_grounded]
    exact hm
  exact ⟨ps', hma, hcompat'⟩

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

-- Soundness of the whole backtracking walk, all in one induction over the
-- body: whatever partial substitution it settles on is functional, extends
-- the one it started from, has bound every variable of every antecedent
-- walked past, and grounds each of those antecedents into something
-- already in `kb`.
theorem matchBody_sound {kb: List GrAtom}:
  ∀ {body: List Atom} {ps ps': PartialSubst},
    ps.Functional →
    ps' ∈ matchBody kb ps body →
    ps'.Functional
  ∧ (∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
  ∧ (∀ b ∈ body, ∀ v ∈ b.vars, ∃ c, (v, c) ∈ ps')
  ∧ (∀ b ∈ body, Subst.grounded b (Subst.ofAssoc ps') ∈ kb)
:= by
  intro body
  induction body with
  | nil =>
    intro ps ps' hfunc hmem
    simp only [matchBody, List.mem_singleton] at hmem
    subst hmem
    refine ⟨hfunc, λ _ _ h ↦ h, ?_, ?_⟩
    · intro b hb; nomatch hb
    · intro b hb; nomatch hb
  | cons b rest ih =>
    intro ps ps' hfunc hmem
    simp only [matchBody, List.mem_flatMap] at hmem
    obtain ⟨g, hg, hmem⟩ := hmem
    cases hma: matchAtom ps b g with
    | none => rw [hma] at hmem; nomatch hmem
    | some ps₁ =>
      rw [hma] at hmem
      obtain ⟨hfunc₁, hsub₁, hvars₁, hg1⟩ := matchAtom_sound hfunc hma
      obtain ⟨hfunc', hsub', hvarsrest, hbodyrest⟩ := ih hfunc₁ hmem
      refine ⟨hfunc', λ v c h ↦ hsub' v c (hsub₁ v c h), λ b' hb' v hv ↦ ?_, λ b' hb' ↦ ?_⟩
      · cases hb' with
        | head _ =>
          obtain ⟨c, hc⟩ := hvars₁ v hv
          exact ⟨c, hsub' v c hc⟩
        | tail _ hb' => exact hvarsrest b' hb' v hv
      · cases hb' with
        | head _ =>
          rw [Atom.grounded_stable hfunc₁ hfunc' hvars₁ hsub' hg1]
          exact hg
        | tail _ hb' => exact hbodyrest b' hb'

-- Completeness of the whole walk: if `σ` fires the body against `kb`, the
-- walk finds SOME partial substitution — not necessarily `σ` itself, but
-- one that agrees with `σ` everywhere it is defined, which is exactly what
-- `matchBody_sound`'s "every variable gets bound" fact plus `hcompat` need
-- to reconstruct `σ`'s ground instance of anything built from this body's
-- variables.
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
    obtain ⟨ps₁, hma, hcompat₁⟩ := matchAtom_complete (a := b) hcompat
    have hfunc₁ := (matchAtom_sound hfunc hma).1
    obtain ⟨ps', hmem', hcompat'⟩ :=
      ih hfunc₁ hcompat₁ (λ b' hb' ↦ hbodykb b' (.tail _ hb'))
    refine ⟨ps', ?_, hcompat'⟩
    simp only [matchBody, List.mem_flatMap]
    refine ⟨Subst.grounded b σ, hgkb, ?_⟩
    simp only [hma]
    exact hmem'

-- The immediate-consequence computation shared by `Program.matchStepAtoms`
-- below and its Herbrand-base-filtered cousin in SlowMatching.lean: every
-- rule's head, grounded by every substitution the backtracking walk finds
-- for its body.
def stepImage (p: Program) (kb: List GrAtom): List GrAtom :=
  p.flatMap λ r ↦ (matchBody kb [] r.body).map λ ps ↦ Subst.grounded r.head (Subst.ofAssoc ps)

-- The bare existence fact, needing nothing about `kb` at all: every atom
-- the walk produces is some rule's head under a substitution whose body
-- fires against `kb`. Shared by `mem_stepImage` below (which additionally
-- confines that substitution to `p.consts`, given `kb` bounded) and by
-- SlowMatching.lean's reachability proof (which needs no such confinement).
theorem mem_stepImage_core {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ stepImage p kb →
    ∃ r ∈ p, ∃ σ: Subst, (∀ b ∈ r.body, Subst.grounded b σ ∈ kb) ∧ a = Subst.grounded r.head σ
:= by
  intro ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨ps, hps, rfl⟩ := List.mem_map.mp ha
  obtain ⟨_, _, _, hbody⟩ := matchBody_sound PartialSubst.functional_nil hps
  exact ⟨r, hr, Subst.ofAssoc ps, hbody, rfl⟩

-- Soundness, in the same shape as `Program.mem_stepAtoms` (Step.lean): with
-- `kb` bounded by the Herbrand base, that substitution is also confined to
-- `p.consts` on the rule's variables — here needing that hypothesis, since
-- (unlike the candidate-substitution approach) the values the substitution
-- takes come from `kb` itself rather than from `p.consts` directly.
theorem mem_stepImage {p: Program} {kb: List GrAtom} {a: GrAtom}
    (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base):
    a ∈ stepImage p kb →
    ∃ r ∈ p, ∃ σ: Subst,
      (∀ v ∈ r.vars, σ v ∈ p.consts)
    ∧ (∀ b ∈ r.body, Subst.grounded b σ ∈ kb)
    ∧ a = Subst.grounded r.head σ
:= by
  intro ha
  obtain ⟨r, hr, σ, hbody, rfl⟩ := mem_stepImage_core ha
  exact ⟨r, hr, σ, Program.subst_consts hbound hbody, hbody, rfl⟩

-- COMPLETENESS: if `σ` fires a rule's body against `kb`, the walk already
-- finds a substitution whose grounding of that rule's head AGREES with
-- `σ`'s. Shared by both `Program.matchStepAtoms` (unconditionally — see
-- `mem_stepImage_of_fires`) and its filtered cousin (which additionally
-- has to check the result survives the filter).
theorem stepImage_grounds_head {kb: List GrAtom} {r: Rule} {σ: Subst}
    (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    ∃ ps' ∈ matchBody kb [] r.body,
      Subst.grounded r.head (Subst.ofAssoc ps') = Subst.grounded r.head σ
:= by
  obtain ⟨ps', hmem', hcompat'⟩ :=
    matchBody_complete PartialSubst.functional_nil (λ v c h ↦ nomatch h) hbody
  obtain ⟨hfunc', _, hvars', _⟩ := matchBody_sound PartialSubst.functional_nil hmem'
  refine ⟨ps', hmem', ?_⟩
  apply Subtype.ext
  apply Atom.ground_congr
  intro v hv
  obtain ⟨b, hb, hbv⟩ := r.safe v hv
  obtain ⟨c, hc⟩ := hvars' b hb v hbv
  rw [PartialSubst.ofAssoc_of_mem hfunc' hc]
  exact (hcompat' v c hc).symm

theorem mem_stepImage_of_fires {p: Program} {r: Rule} {σ: Subst} {kb: List GrAtom}
    (hr: r ∈ p) (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    Subst.grounded r.head σ ∈ stepImage p kb
:= by
  obtain ⟨ps', hmem', heq⟩ := stepImage_grounds_head hbody
  rw [← heq]
  exact List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨ps', hmem', rfl⟩⟩

end Matching

def Program.matchStepAtoms (p: Program) (kb: List GrAtom): List GrAtom :=
  Matching.stepImage p kb

theorem Program.mem_matchStepAtoms {p: Program} {kb: List GrAtom} {a: GrAtom}
    (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base):
    a ∈ p.matchStepAtoms kb →
    ∃ r ∈ p, ∃ σ: Subst,
      (∀ v ∈ r.vars, σ v ∈ p.consts)
    ∧ (∀ b ∈ r.body, Subst.grounded b σ ∈ kb)
    ∧ a = Subst.grounded r.head σ
:= Matching.mem_stepImage hbound

-- ...and so, exactly as for `Program.stepAtoms`, everything the walk
-- produces lands in the Herbrand base — given `kb` already does.
theorem Program.matchStepAtoms_mem_herbrand_base {p: Program} {kb: List GrAtom} {a: GrAtom}
    (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base):
    a ∈ p.matchStepAtoms kb →
    a ∈ p.herbrand_base
:= by
  intro ha
  obtain ⟨r, hr, σ, hcs, _, rfl⟩ := Program.mem_matchStepAtoms hbound ha
  exact Program.grounded_head_mem_herbrand_base hr hcs

-- COMPLETENESS: if any substitution fires a rule against `kb`, the walk
-- already produces that head — the payoff of matching rather than blind
-- enumeration. Unlike `Program.mem_stepAtoms_of_fires` (Step.lean), this
-- needs no boundedness hypothesis on `kb` at all: the walk searches `kb`
-- directly rather than reconstructing a `p.consts`-confined candidate, so
-- there is nothing to confine.
theorem Program.mem_matchStepAtoms_of_fires {p: Program} {r: Rule} {σ: Subst} {kb: List GrAtom}
    (hr: r ∈ p) (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    Subst.grounded r.head σ ∈ p.matchStepAtoms kb
:= Matching.mem_stepImage_of_fires hr hbody

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

example: prog.matchStepAtoms []   = [pa]     := by decide
example: prog.matchStepAtoms [pa] = [pa, qa] := by decide

namespace Matching

/-
Saturation itself, fuelled rather than well-founded.

Each tick is one `Program.matchStepAtoms` call, exactly like Stepwise.lean's
loop — the only difference is what makes it terminate. Stepwise.lean lets
Lean's well-founded recursion track the decreasing "unseen Herbrand-base
atoms" measure directly, because `Program.stepAtoms_mem_herbrand_base` needs
no hypothesis on `kb`. `Program.matchStepAtoms_mem_herbrand_base` above
DOES need `kb` already bounded, and that fact is only available inside a
correctness proof, not at the point `saturateGo` is defined — threading it
through a `termination_by` obligation runs into a real limitation of Lean's
equation compiler (the recursive call's auto-generated proof term does not
survive being generalised for a later rewrite in `saturateGo_fixpoint`
below). Fuelling the recursion with a `Nat` sidesteps this: a plain
structural recursion on `Nat` needs no termination proof at all, so
boundedness becomes an ordinary post-hoc induction instead of a proof
obligation baked into the definition. `p.herbrand_base.length` is always
enough fuel; `saturateGo_fixpoint` is where that gets made precise, via the
same strictly-decreasing-unseen-count measure Stepwise.lean's
`termination_by` uses:

  fuel   3        2         1           0
        kb ──▸ {a} ──▸ {a,b} ──▸ {a,b,c} ──▸ {a,b,c}   (find? = none: done early)
             +a       +b         +c              ◂── remaining fuel goes unused
-/
def saturateGo (p: Program): Nat → List GrAtom → List GrAtom
  | 0, kb => kb
  | n+1, kb =>
    match (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => kb
    | some a => saturateGo p n (a :: kb)

def saturate (p: Program): List GrAtom :=
  saturateGo p p.herbrand_base.length []

-- The Herbrand bound is an invariant of the loop, for any amount of fuel:
-- an under-fuelled run just stops early at some earlier bounded `kb`.
theorem saturateGo_bounded (p: Program):
  ∀ n kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    ∀ g ∈ saturateGo p n kb, g ∈ p.herbrand_base
:= by
  intro n
  induction n with
  | zero => intro kb hb g hg; exact hb g hg
  | succ n ih =>
    intro kb hb g hg
    simp only [saturateGo] at hg
    cases hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => rw [hfind] at hg; exact hb g hg
    | some a =>
      rw [hfind] at hg
      refine ih (a :: kb) (λ g' hg' ↦ ?_) g hg
      cases hg' with
      | head _ => exact Program.matchStepAtoms_mem_herbrand_base hb (List.mem_of_find?_eq_some hfind)
      | tail _ hg' => exact hb g' hg'

-- Each iteration is one `infer` step, so the result stays reachable — again
-- for any amount of fuel.
theorem saturateGo_reachable (p: Program):
  ∀ n kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    p.infer.ReflTransGen ∅ (λ g ↦ g ∈ kb) →
    p.infer.ReflTransGen ∅ (λ g ↦ g ∈ saturateGo p n kb)
:= by
  intro n
  induction n with
  | zero => intro kb _ h; exact h
  | succ n ih =>
    intro kb hb h
    simp only [saturateGo]
    cases hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => exact h
    | some a =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hb': ∀ g ∈ a :: kb, g ∈ p.herbrand_base := by
        intro g hg
        cases hg with
        | head _ => exact Program.matchStepAtoms_mem_herbrand_base hb hmem
        | tail _ hg => exact hb g hg
      refine ih (a :: kb) hb' (.snoc _ _ _ h ?_)
      obtain ⟨r, hr, σ, _, hbody, rfl⟩ := Program.mem_matchStepAtoms hb hmem
      have hnew := List.find?_some hfind
      simp only [decide_eq_true_iff] at hnew
      exact ⟨r, hr, σ, hbody, hnew, Set.ofList_cons⟩

-- The loop returns only at a fixpoint, PROVIDED it started with enough
-- fuel: the count of not-yet-known Herbrand-base atoms strictly drops each
-- tick that finds something new (exactly Stepwise.lean's termination
-- measure), so fuel bounding that count from above can never run out
-- before a genuine fixpoint is reached.
theorem saturateGo_fixpoint (p: Program):
  ∀ n kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    p.herbrand_base.countP (λ b ↦ decide (b ∉ kb)) ≤ n →
    ∀ a ∈ p.matchStepAtoms (saturateGo p n kb), a ∈ saturateGo p n kb
:= by
  intro n
  induction n with
  | zero =>
    intro kb hb hfuel a ha
    have habase := Program.matchStepAtoms_mem_herbrand_base hb ha
    have hz: p.herbrand_base.countP (λ b ↦ decide (b ∉ kb)) = 0 := by omega
    have hmemkb: a ∈ kb := by simpa using List.countP_eq_zero.mp hz a habase
    exact hmemkb
  | succ n ih =>
    intro kb hb hfuel
    simp only [saturateGo]
    cases hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none =>
      intro a ha
      simpa using List.find?_eq_none.mp hfind a ha
    | some a =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hnew: a ∉ kb := by simpa using List.find?_some hfind
      have hb': ∀ g ∈ a :: kb, g ∈ p.herbrand_base := by
        intro g hg
        cases hg with
        | head _ => exact Program.matchStepAtoms_mem_herbrand_base hb hmem
        | tail _ hg => exact hb g hg
      have hdec: p.herbrand_base.countP (λ b ↦ decide (b ∉ a :: kb)) <
                 p.herbrand_base.countP (λ b ↦ decide (b ∉ kb)) := by
        refine List.countP_lt_countP (a := a)
          ?_ (Program.matchStepAtoms_mem_herbrand_base hb hmem) ?_ ?_
        · intro x _ hx
          simp only [decide_eq_true_iff] at hx ⊢
          exact λ hgx ↦ hx (.tail _ hgx)
        · simpa using hnew
        · simp only [decide_eq_true_iff]
          exact λ hh ↦ hh (.head _)
      exact ih (a :: kb) hb' (by omega)

theorem saturate_model (p: Program):
    p.model (· ∈ saturate p)
:= by
  have hbound := saturateGo_bounded p p.herbrand_base.length [] (λ g hg ↦ nomatch hg)
  constructor
  · refine saturateGo_reachable p p.herbrand_base.length [] (λ g hg ↦ nomatch hg) ?_
    rw [Set.ofList_nil]
    exact .refl _
  · rintro ⟨kb', r, hr, σ, hfires, hnew, _⟩
    exact hnew (saturateGo_fixpoint p p.herbrand_base.length [] (λ g hg ↦ nomatch hg)
      List.countP_le_length _
      (Program.mem_matchStepAtoms_of_fires hr hfires))

def evaluator: Evaluator := ⟨saturate, saturate_model⟩

end Matching
