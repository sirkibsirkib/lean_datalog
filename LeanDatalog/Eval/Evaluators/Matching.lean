import LeanDatalog.Eval.Step
import LeanDatalog.Eval.Interface

/-
Saturation by backtracking search instead of enumeration.

`Program.stepAtoms` (Step.lean) tries every assignment of `p.consts` to a
rule's variables, costing `C^V` per rule whatever `kb` holds. This module
walks a rule's body left to right instead, trying each atom against every
element of `kb` and growing a partial variable assignment, backtracking as
soon as two atoms disagree about a variable. For `body = [p(X,Y), q(Y)]`
against `kb = {g₁, g₂, g₃}`:

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

The partial assignment `Variable → Option Constant` is an assoc list
(`PartialSubst`), read exactly as `Subst.ofAssoc` reads one: no entry means
`none`.
-/

-- A ground atom's `args` are all `.inr`, so `consts` recovers them in order.
private theorem args_eq_consts_map_inr_aux:
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

private theorem filterMap_ground_aux {σ: Subst}:
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

-- The converse direction: the constants of `a` grounded by `σ`, in order.
theorem Atom.consts_grounded {a: Atom} {σ: Subst}:
    (Subst.grounded a σ).val.consts = a.args.map (λ arg ↦ Arg.grounding arg σ)
:= filterMap_ground_aux

namespace Matching

abbrev PartialSubst := List (Variable × Constant)

def PartialSubst.lookup (ps: PartialSubst) (v: Variable): Option Constant :=
  (ps.find? (λ pr ↦ pr.1 == v)).map Prod.snd

-- At most one value per variable. `matchArg` only adds an entry for a
-- variable `lookup` reports absent, so everything built here keeps this.
def PartialSubst.Functional (ps: PartialSubst): Prop :=
  ∀ v c c', (v, c) ∈ ps → (v, c') ∈ ps → c = c'

theorem PartialSubst.functional_nil: PartialSubst.Functional [] :=
  λ _ _ _ h _ ↦ nomatch h

-- Match one argument against the constant in the same position of a ground
-- atom: a constant must equal it, a bound variable must agree with it, and
-- an unbound variable gets bound to it.
def matchArg (ps: PartialSubst) (pat: Arg) (val: Constant): Option PartialSubst :=
  match pat with
  | .inr c => if c = val then some ps else none
  | .inl v =>
    match ps.lookup v with
    | some c => if c = val then some ps else none
    | none => some ((v, val) :: ps)

-- Match argument lists pointwise, threading the assignment left to right.
-- Arity is not enforced by the types, so a length mismatch fails.
def matchArgs (ps: PartialSubst): List Arg → List Constant → Option PartialSubst
  | [], [] => some ps
  | pat :: pats, val :: vals =>
    (matchArg ps pat val).bind λ ps' ↦ matchArgs ps' pats vals
  | [], _ :: _ => none
  | _ :: _, [] => none

def matchAtom (ps: PartialSubst) (a: Atom) (g: GrAtom): Option PartialSubst :=
  if a.pred = g.val.pred then matchArgs ps a.args g.val.consts else none

-- Every assignment matching the whole body against `kb`. `flatMap` is the
-- backtracking: a failed match contributes nothing, and every other `g` is
-- still tried.
def matchBody (kb: List GrAtom) (ps: PartialSubst):
    List Atom → List PartialSubst
  | [] => [ps]
  | a :: rest =>
    kb.flatMap λ g ↦
      match matchAtom ps a g with
      | some ps' => matchBody kb ps' rest
      | none => []

theorem PartialSubst.lookup_mem {ps: PartialSubst} {v: Variable} {c: Constant}
    (h: ps.lookup v = some c): (v, c) ∈ ps
:= by
  obtain ⟨⟨v', c'⟩, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  have hv: v' = v := Subtype.ext (by simpa using List.find?_some hfind)
  exact hv ▸ List.mem_of_find?_eq_some hfind

theorem PartialSubst.lookup_eq_none {ps: PartialSubst} {v: Variable}
    (h: ps.lookup v = none) (c: Constant): (v, c) ∉ ps
:= λ hmem ↦ absurd (List.find?_eq_none.mp (Option.map_eq_none_iff.mp h) _ hmem) (by simp)

theorem PartialSubst.ofAssoc_of_mem {ps: PartialSubst} {v: Variable} {c: Constant}
    (hfunc: ps.Functional) (hmem: (v, c) ∈ ps):
    Subst.ofAssoc ps v = c
:= by
  obtain ⟨⟨v', c'⟩, hpr, hpr1, heq⟩ := Subst.ofAssoc_spec (l := ps) ⟨(v, c), hmem, rfl⟩
  simp only at hpr1
  rw [heq]
  exact (hfunc v c c' hmem (hpr1 ▸ hpr)).symm

-- The three ways `matchArg` can succeed, so later proofs need not re-unfold it.
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

-- A successful argument match keeps the assignment functional, only grows
-- it, and leaves the pattern agreeing with `val`.
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
    · -- the new binding is for a variable `lookup` found absent, so it
      -- cannot clash with anything already there
      intro v₁ c₁ c₂ h₁ h₂
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

-- Completeness for one argument: matching against the value `σ` gives it
-- never fails, provided the assignment so far agrees with `σ`.
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

-- ...and the result still agrees with `σ`: the only possible new entry binds
-- `pat` to its own value under `σ`.
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

-- `matchArg_sound` across an argument list, plus the payoff: the final
-- assignment grounds the patterns to exactly `vals`. Being one equation
-- about one substitution, it handles repeated variables for free.
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

-- Completeness across an argument list.
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
    obtain ⟨ps', hrest, hcompat'⟩ := ih (matchArg_compat hcompat rfl hm)
    refine ⟨ps', ?_, hcompat'⟩
    simp only [List.map_cons, matchArgs, Option.bind_eq_some_iff]
    exact ⟨ps₁, hm, hrest⟩

-- `matchArgs_sound` for a whole atom: success grounds `a` to exactly `g`.
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

-- Completeness for an atom: matching `a` against its own image under `σ`
-- succeeds.
theorem matchAtom_complete {ps: PartialSubst} {a: Atom} {σ: Subst}
    (hcompat: ∀ v c, (v, c) ∈ ps → σ v = c):
    ∃ ps', matchAtom ps a (Subst.grounded a σ) = some ps'
    ∧ (∀ v c, (v, c) ∈ ps' → σ v = c)
:= by
  obtain ⟨ps', hm, hcompat'⟩ := matchArgs_succeeds (ps := ps) (σ := σ) (pats := a.args) hcompat
  have hpred: a.pred = (Subst.grounded a σ).val.pred := rfl
  refine ⟨ps', ?_, hcompat'⟩
  simp only [matchAtom]
  rw [if_pos hpred, Atom.consts_grounded]
  exact hm

-- Growing a functional assignment cannot change how an atom grounds once
-- its variables are all bound.
theorem grounded_stable {b: Atom} {ps ps': PartialSubst} {g: GrAtom}
    (hpsf: ps.Functional) (hpsf': ps'.Functional)
    (hvars: ∀ v ∈ b.vars, ∃ c, (v, c) ∈ ps)
    (hsub: ∀ v c, (v, c) ∈ ps → (v, c) ∈ ps')
    (heq: Subst.grounded b (Subst.ofAssoc ps) = g):
    Subst.grounded b (Subst.ofAssoc ps') = g
:= by
  rw [← heq]
  refine Subtype.ext (Atom.ground_congr λ v hv ↦ ?_)
  obtain ⟨c, hc⟩ := hvars v hv
  rw [PartialSubst.ofAssoc_of_mem hpsf' (hsub v c hc), PartialSubst.ofAssoc_of_mem hpsf hc]

-- Soundness of the walk: the assignment it ends on is functional, extends
-- the starting one, binds every body variable, and grounds every body atom
-- into `kb`.
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
        | head _ => exact grounded_stable hfunc₁ hfunc' hvars₁ hsub' hg1 ▸ hg
        | tail _ hb' => exact hbodyrest b' hb'

-- Completeness of the walk: if `σ` grounds the body into `kb`, the walk finds
-- an assignment agreeing with `σ` wherever it is defined.
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
    intro ps _ hcompat _
    exact ⟨ps, .head _, hcompat⟩
  | cons b rest ih =>
    intro ps hfunc hcompat hbodykb
    obtain ⟨ps₁, hma, hcompat₁⟩ := matchAtom_complete (a := b) hcompat
    obtain ⟨ps', hmem', hcompat'⟩ :=
      ih (matchAtom_sound hfunc hma).1 hcompat₁ (λ b' hb' ↦ hbodykb b' (.tail _ hb'))
    refine ⟨ps', ?_, hcompat'⟩
    simp only [matchBody, List.mem_flatMap]
    refine ⟨Subst.grounded b σ, hbodykb b (.head _), ?_⟩
    simp only [hma]
    exact hmem'

end Matching

-- Every rule's head, grounded by every assignment the walk finds for its body.
def Program.matchStepAtoms (p: Program) (kb: List GrAtom): List GrAtom :=
  p.flatMap λ r ↦
    (Matching.matchBody kb [] r.body).map λ ps ↦ Subst.grounded r.head (Subst.ofAssoc ps)

-- Soundness: every atom produced is a rule's head under a substitution whose
-- body is already known.
theorem Program.mem_matchStepAtoms {p: Program} {kb: List GrAtom} {a: GrAtom}:
    a ∈ p.matchStepAtoms kb →
    ∃ r ∈ p, ∃ σ: Subst, (∀ b ∈ r.body, Subst.grounded b σ ∈ kb) ∧ a = Subst.grounded r.head σ
:= by
  intro ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨ps, hps, rfl⟩ := List.mem_map.mp ha
  exact ⟨r, hr, _, (Matching.matchBody_sound Matching.PartialSubst.functional_nil hps).2.2.2, rfl⟩

-- Values come from `kb` rather than `p.consts`, so staying in the Herbrand
-- base needs `kb` to be in it already — unlike `Program.stepAtoms`.
theorem Program.matchStepAtoms_mem_herbrand_base {p: Program} {kb: List GrAtom} {a: GrAtom}
    (hbound: ∀ g ∈ kb, g ∈ p.herbrand_base):
    a ∈ p.matchStepAtoms kb →
    a ∈ p.herbrand_base
:= by
  intro ha
  obtain ⟨r, hr, σ, hbody, rfl⟩ := Program.mem_matchStepAtoms ha
  exact Rule.fires_head_mem_herbrand_base (kb := (· ∈ kb)) hr hbound hbody

-- Completeness: whatever substitution fires a rule, the walk finds an
-- assignment grounding the head the same way. No bound on `kb` is needed,
-- since the walk searches `kb` itself.
theorem Program.mem_matchStepAtoms_of_fires {p: Program} {r: Rule} {σ: Subst} {kb: List GrAtom}
    (hr: r ∈ p) (hbody: ∀ b ∈ r.body, Subst.grounded b σ ∈ kb):
    Subst.grounded r.head σ ∈ p.matchStepAtoms kb
:= by
  obtain ⟨ps, hmem, hcompat⟩ :=
    Matching.matchBody_complete Matching.PartialSubst.functional_nil (λ _ _ h ↦ nomatch h) hbody
  obtain ⟨hfunc, _, hvars, _⟩ := Matching.matchBody_sound Matching.PartialSubst.functional_nil hmem
  have heq: Subst.grounded r.head (Subst.ofAssoc ps) = Subst.grounded r.head σ := by
    refine Subtype.ext (Atom.ground_congr λ v hv ↦ ?_)
    obtain ⟨b, hb, hbv⟩ := r.safe v hv
    obtain ⟨c, hc⟩ := hvars b hb v hbv
    rw [Matching.PartialSubst.ofAssoc_of_mem hfunc hc, hcompat v c hc]
  exact heq ▸ List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨ps, hmem, rfl⟩⟩

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
Saturation, one atom per tick as in Stepwise.lean, but recursing on fuel
rather than well-founded on the count of unknown base atoms.

The well-founded version would need `matchStepAtoms_mem_herbrand_base` in its
`decreasing_by`, and that lemma needs `kb` bounded — a fact the definition
cannot see without carrying a proof in its arguments, which breaks rewriting
with the generated equation lemmas. Structural recursion on `Nat` needs no
termination proof, so boundedness becomes an ordinary induction instead.
`p.herbrand_base.length` fuel always suffices (`saturateGo_fixpoint`), and a
run stops as soon as nothing is new, leaving the rest unused:

  fuel   3        2         1           0
        ∅ ──▸ {a} ──▸ {a,b} ──▸ {a,b,c}
            +a       +b         +c       find? = none: done
-/
def saturateGo (p: Program): Nat → List GrAtom → List GrAtom
  | 0, kb => kb
  | n+1, kb =>
    match (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => kb
    | some a => saturateGo p n (a :: kb)

def saturate (p: Program): List GrAtom :=
  saturateGo p p.herbrand_base.length []

theorem bounded_cons {p: Program} {kb: List GrAtom} {a: GrAtom}
    (hb: ∀ g ∈ kb, g ∈ p.herbrand_base) (ha: a ∈ p.matchStepAtoms kb):
    ∀ g ∈ a :: kb, g ∈ p.herbrand_base
:= List.forall_mem_cons.mpr ⟨Program.matchStepAtoms_mem_herbrand_base hb ha, hb⟩

-- The Herbrand bound is an invariant, whatever the fuel.
theorem saturateGo_bounded (p: Program):
  ∀ n kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    ∀ g ∈ saturateGo p n kb, g ∈ p.herbrand_base
:= by
  intro n
  induction n with
  | zero => exact λ _ hb ↦ hb
  | succ n ih =>
    intro kb hb
    simp only [saturateGo]
    cases hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => exact hb
    | some a => exact ih _ (bounded_cons hb (List.mem_of_find?_eq_some hfind))

-- Each tick is one `infer` step, so the result stays reachable, whatever the
-- fuel.
theorem saturateGo_reachable (p: Program):
  ∀ n kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    p.infer.ReflTransGen ∅ (· ∈ kb) →
    p.infer.ReflTransGen ∅ (· ∈ saturateGo p n kb)
:= by
  intro n
  induction n with
  | zero => exact λ _ _ h ↦ h
  | succ n ih =>
    intro kb hb h
    simp only [saturateGo]
    cases hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => exact h
    | some a =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hnew: a ∉ kb := by simpa using List.find?_some hfind
      obtain ⟨r, hr, σ, hbody, rfl⟩ := Program.mem_matchStepAtoms hmem
      exact ih _ (bounded_cons hb hmem) (.snoc _ _ _ h (Program.infer_cons hr hbody hnew))

-- With fuel at least the number of unknown base atoms, the run ends at a
-- fixpoint: every tick that finds something new uses one unit of each.
theorem saturateGo_fixpoint (p: Program):
  ∀ n kb, (∀ g ∈ kb, g ∈ p.herbrand_base) →
    p.herbrand_base.countP (λ b ↦ decide (b ∉ kb)) ≤ n →
    ∀ a ∈ p.matchStepAtoms (saturateGo p n kb), a ∈ saturateGo p n kb
:= by
  intro n
  induction n with
  | zero =>
    -- no base atom is unknown, and everything produced is a base atom
    intro kb hb hfuel a ha
    show a ∈ kb
    simpa using List.countP_eq_zero.mp (Nat.le_zero.mp hfuel) a
      (Program.matchStepAtoms_mem_herbrand_base hb ha)
  | succ n ih =>
    intro kb hb hfuel
    simp only [saturateGo]
    cases hfind: (p.matchStepAtoms kb).find? (λ a ↦ decide (a ∉ kb)) with
    | none => exact λ a ha ↦ by simpa using List.find?_eq_none.mp hfind a ha
    | some a =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hdec := List.countP_not_mem_lt (λ _ h ↦ .tail _ h)
        (Program.matchStepAtoms_mem_herbrand_base hb hmem)
        (by simpa using List.find?_some hfind) (.head _)
      exact ih _ (bounded_cons hb hmem) (by omega)

theorem saturate_model (p: Program):
    p.model (· ∈ saturate p)
:= by
  have hnil: ∀ g ∈ ([]: List GrAtom), g ∈ p.herbrand_base := λ _ h ↦ nomatch h
  exact Program.model_of_closed (saturateGo_reachable p _ [] hnil p.reachable_nil)
    λ _ hr _ hf ↦ saturateGo_fixpoint p _ [] hnil List.countP_le_length _
      (Program.mem_matchStepAtoms_of_fires hr hf)

def evaluator: Evaluator := ⟨saturate, saturate_model⟩

end Matching
