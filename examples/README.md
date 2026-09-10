# Examples

Run one by piping it in:

```sh
lake build
./.lake/build/bin/lean_datalog < examples/reachability.lp
```

The program is read from stdin, parsed, saturated, and the derived atoms are
printed sorted, one per line. A malformed program exits 1 with a message on
stderr.

A `%` starts a comment running to the end of the line. Comments are accepted
anywhere whitespace is, so mid-rule and mid-argument-list are both fine.

| file | what it shows |
| --- | --- |
| `reachability.lp` | transitive closure over a chain — the canonical Datalog program |
| `cycle.lp` | the same rules over a *cyclic* graph, so recursion terminates only because saturation reaches a fixpoint |
| `same_generation.lp` | non-linear recursion (the recursive atom is not the first body atom) |
| `propositional.lp` | zero-arg atoms, where the parens may be dropped: `rain.` and `rain().` are the same atom |

## Syntax

- A `%` begins a line comment, legal wherever whitespace is.
- An identifier starting **lowercase** is a constant or predicate name; one
  starting **uppercase** is a variable.
- An atom is `pred(arg, ...)`, with the parens optional when there are no
  arguments.
- A rule is `head :- body1, body2.` and a fact is just `head.`
- Rules must be **range-restricted**: every variable in the head has to occur
  in the body. `p(X) :- q(a).` is rejected, because there would be infinitely
  many ground instances of it.
