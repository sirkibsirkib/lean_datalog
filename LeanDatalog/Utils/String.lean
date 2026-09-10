-- Does `s` start with a character satisfying `f`? False for the empty
-- string, which is what makes it usable as a subtype predicate.
def String.first_with (f: Char → Bool) (s: String): Bool :=
  (String.Pos.Raw.get? s 0).elim false f
