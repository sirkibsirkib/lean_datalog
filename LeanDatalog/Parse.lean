import LeanDatalog.Syntax

/-
A small hand-rolled recursive-descent parser for Datalog programs.

Identifiers starting with a lowercase letter parse as `Constant`s, those
starting with an uppercase letter parse as `Variable`s (matching the
`first_with`-based encoding in Syntax.lean exactly). Atoms are
`pred(arg, ...)`, with the parens optional when there are no args (`p` and
`p()` are the same atom); rules are `head :- body, ....` or a bare fact
`head.`. A `%` starts a comment running to the end of the line, accepted
anywhere whitespace is.

Parsers take a `List Char` and return the parsed value with the remainder
(just the remainder, for punctuation). Most recurse structurally on that
list. The loops that call back out to another parser (`commaListGo` and
`program`) can't, so they recurse on `Nat` fuel seeded with the input length.
-/

-- `none` when `head :- body` isn't range-restricted, i.e. `Rule.Safe` fails.
def Rule.ofHeadBody? (head: Atom) (body: List Atom): Option Rule :=
  if h: Rule.Safe head body
  then some { head, body, safe := h }
  else none

namespace Parse

def isIdentStart (c: Char): Bool := c.isAlpha
def isIdentChar  (c: Char): Bool := c.isAlphanum || c == '_'

-- Whitespace and `%` line comments. Every parser reaches its token through
-- `skipWs`, so comments are legal exactly where whitespace is.
--
-- Mutual recursion keeps both structurally recursive; `skipWs (cs.dropWhile
-- ...)` would need a well-founded measure.
mutual

  def skipWs: List Char → List Char
    | c :: cs =>
      if c.isWhitespace then skipWs cs
      else if c == '%' then skipComment cs
      else c :: cs
    | [] => []

  -- A comment runs to the newline, or to end of input if there is none.
  def skipComment: List Char → List Char
    | '\n' :: cs => skipWs cs
    | _ :: cs => skipComment cs
    | [] => []

end

def identGo: List Char → String → String × List Char
  | c :: cs, acc => if isIdentChar c then identGo cs (acc.push c) else (acc, c :: cs)
  | [], acc => (acc, [])

def ident: List Char → Option (String × List Char)
  | c :: cs => if isIdentStart c then some (identGo (c :: cs) "") else none
  | [] => none

-- Punctuation carries no value worth keeping, so these yield just the rest.
def char1 (c: Char): List Char → Option (List Char)
  | c' :: cs => if c' == c then some cs else none
  | [] => none

def implies (cs: List Char): Option (List Char) := do
  let cs ← char1 ':' cs
  char1 '-' cs

-- Shared by `const` and `var`, which differ only in which first-letter
-- predicate the identifier must satisfy.
def identWith (P: Char → Bool) (cs: List Char):
    Option ({s: String // s.first_with P} × List Char) := do
  let (s, cs) ← ident cs
  if h: s.first_with P then some (⟨s, h⟩, cs) else none

def const (cs: List Char): Option (Constant × List Char) := identWith Char.isLower cs

def var   (cs: List Char): Option (Variable × List Char) := identWith Char.isUpper cs

-- `var` and `const` are mutually exclusive (upper- vs lowercase first letter),
-- so falling back from one to the other can't lose a parse.
def arg (cs: List Char): Option (Arg × List Char) :=
  (var cs).map (λ (v, cs) ↦ (.inl v, cs)) <|>
    (const cs).map (λ (c, cs) ↦ (.inr c, cs))

-- Parses a tail `, x, y, ...` with item parser `p`, stopping once no comma
-- follows. Each iteration consumes at least a comma, so input length is
-- enough fuel.
def commaListGo {α: Type} (p: List Char → Option (α × List Char)):
    Nat → List Char → Option (List α × List Char)
  | 0, cs => some ([], cs)
  | n + 1, cs =>
    let cs := skipWs cs
    match char1 ',' cs with
    | some cs => do
      let (a, cs) ← p (skipWs cs)
      let (as, cs) ← commaListGo p n cs
      some (a :: as, cs)
    | none => some ([], cs)

def argListGo (cs: List Char): Option (List Arg × List Char) :=
  commaListGo arg cs.length cs

-- `pred(args)` allows zero args, so `arg` failing here isn't a parse failure.
def argList (cs: List Char): Option (List Arg × List Char) :=
  match arg (skipWs cs) with
  | none => some ([], cs)
  | some (a, cs) => do
    let (as, cs) ← argListGo cs
    some (a :: as, cs)

-- A predicate name is spelled exactly like a constant, so `const` does the
-- lowercase-first check.
def atom (cs: List Char): Option (Atom × List Char) := do
  let (pred, cs) ← const (skipWs cs)
  -- A zero-arg atom may omit the parens: `p` and `p()` are the same atom.
  let (args, cs) ← match char1 '(' (skipWs cs) with
    | some cs => do
      let (args, cs) ← argList cs
      let cs ← char1 ')' (skipWs cs)
      some (args, cs)
    | none => some ([], cs)
  some ({ pred, args }, cs)

def atomListGo (cs: List Char): Option (List Atom × List Char) :=
  commaListGo atom cs.length cs

-- Unlike `argList`, a rule body needs at least one atom, so `atom` failing
-- here fails the whole parse.
def atomList (cs: List Char): Option (List Atom × List Char) := do
  let (a, cs) ← atom cs
  let (as, cs) ← atomListGo cs
  some (a :: as, cs)

def rule (cs: List Char): Option (Rule × List Char) := do
  let (head, cs) ← atom cs
  let cs := skipWs cs
  -- A bare fact `head.` is just a rule with an empty body.
  let (body, cs) ← match implies cs with
    | some cs => atomList (skipWs cs)
    | none => some ([], cs)
  let cs ← char1 '.' (skipWs cs)
  let r ← Rule.ofHeadBody? head body
  some (r, cs)

-- Each iteration consumes a whole rule, so input length is enough fuel.
def program (cs: List Char): Option (Program × List Char) :=
  go cs.length cs
where
  go: Nat → List Char → Option (Program × List Char)
    | 0, cs => some ([], cs)
    | n + 1, cs =>
      match skipWs cs with
      | [] => some ([], [])
      | cs => do
        let (r, cs) ← rule cs
        let (rs, cs) ← go n cs
        some (r :: rs, cs)

end Parse

def parseProgram (s: String): Option Program :=
  (Parse.program s.toList).map Prod.fst

example: (parseProgram "").isSome := by decide

example:
  (parseProgram "
    edge(a, b).
    edge(b, c).
    path(X, Y) :- edge(X, Y).
    path(X, Z) :- path(X, Y), edge(Y, Z).
").isSome := by decide

example: (parseProgram "p").isNone := by decide
example: (parseProgram "p().").isSome := by decide

-- Dropping the parens off a zero-arg atom parses to the very same program.
example: parseProgram "p." = parseProgram "p()." := by decide
example: parseProgram "q :- p." = parseProgram "q() :- p()." := by decide

-- A `%` comment is invisible to the grammar, wherever whitespace may go.
example: parseProgram "% a comment\np(a)." = parseProgram "p(a)." := by decide
example: parseProgram "p(a). % trailing" = parseProgram "p(a)." := by decide
example: parseProgram "p(%c\na)." = parseProgram "p(a)." := by decide
example:
  parseProgram "q(X) %mid-rule\n :- p(X)." = parseProgram "q(X) :- p(X)." := by decide

-- A comment need not be terminated by a newline...
example: (parseProgram "p(a). % unterminated").isSome := by decide
-- ...and a program that is nothing but a comment is the empty program.
example: parseProgram "% nothing here" = parseProgram "" := by decide
