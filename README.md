# Datalog Interpreter in Lean4

This repository contains a Datalog language specification and interpreter implementation, all in Lean4.
The interpreter is compilable to a native binary; the user can execute it with any given Datalog program as input.
Also in Lean, we have formalised the correctness of Datalog interpreters in general, and proven the correcness of our interpreter in particular; the user can let their Local lean installation verify this themselves.

Our specification and implementation aim to present a small, human-readable surface for our formalisation of the language, its notion of correctness, and operation of our interpreter.
To this end, we have tried to present a small and self-contained surface; we have no dependencies beyond the Lean standard library (e.g., we define `Set`). 
Also, we have stayed as close as possible to textbook Datalog terminology (including "ground" and "atom") and algorithms (naive buttom-up fixpoint evaluation).

> Note: this repo was built with extensive assistance from Claude (Model Opus v5); it also served as my first real foray into using this kind of AI assistance for writing Lean. But rest assured that I have scrutinised the result at least as much as I expect you to, and have prodded and poked throughout, and (re)done some parts by hand, to my own satisfaction. -- Christopher Esterhuyse, 9 Sept. 2026. 

## Language Specification

Datalog here is the usual pure fragment: no negation, no arithmetic, no
aggregation, no function symbols. What is formalised is syntax, grounding,
and the least-model semantics.

Two files carry the specification, and they are deliberately small:

- **`LeanDatalog/Syntax.lean`** (73 lines) — `Constant`, `Variable`, `Atom`,
  `Rule`, `Program`. Note that `Rule` carries its **range-restriction**
  obligation as a field: a rule cannot be constructed unless every variable
  of the head also occurs in the body. Safety is therefore expressed already in the abstract syntax, and the parser proves safety or rejects the input. From another point of view, we interleave what may otherwise be separated into parsing and static analysis.
- **`LeanDatalog/Semantics.lean`** (58 lines) — `Rule.fires`,
  `Program.infer`, `Program.model`. Everything is `Prop`-valued: no
  `Option`, no `if`, nothing that computes.

```lean
def Program.infer (p: Program) (kb kb': Kb): Prop :=
  ∃ r ∈ p, ∃ σ: Subst,
    r.fires σ kb
  ∧ σ.grounded r.head ∉ kb
  ∧ kb' = kb ∪ {σ.grounded r.head}

def Program.model (p: Program) (kb: Kb): Prop :=
  p.infer.ReflTransGen ∅ kb
∧ p.infer.Normal kb
```


To be convinced that this is Datalog, the reader should scrutinise these files
plus `Ground.lean` (84 lines, which defines how variables are substituted in rules).
The remaining files can be ignored, because they necessarily preserve the definition of the language.

`Program.model` formalises two familiar features of Datalog, which are spelled out in `SemanticProps.lean`:
- `Program.model_unique`: A program has **at most** one model (from confluence).
- `Program.model_exists`: A program has **at least** one model (from termination).

## Interpreter Implementation

An executable Datalog interpreter is defined atop the language specification.
It is executable in the traditional sense; `lake build` produces a binary that
reads a program on stdin and writes the derived atoms to stdout.
For ease of use, they are printed one per line, sorted alphabetically.

### Building from Source

To install the Lean toolchain locally, follow the instructions at `https://lean-lang.org/install`. We have pinned v4.33.1 for the sake of stability, but you can try updating it in `lean-toolchain`.


Compile the interpreter (with optimisations by default) with

```sh
lake build
```

Thereafter, the binary is available at `./.lake/build/bin/lean_datalog`. Give it a go with some of the provided example Datalog programs. Consult the `examples` directory for an examples-driven look at the Datalog language.

```sh
./.lake/build/bin/lean_datalog < examples/reachability.lp
```

Alternatively, `lake exe lean_datalog < examples/reachability.lp` is a convenient way to compile and run at once.

### Evaluator Modules

We have characterised the core of a Datalog implementation as any _evaluator_: given a program, it builds the model.

```lean
structure Evaluator where
  saturate: Program → List GrAtom
  model: ∀ p: Program, p.model (· ∈ saturate p)
```


Different evaluators exist, representing different inference algorithms, different internal representations, and so on.
We have included two evaluators in `Eval/Evaluators/`, encoding two well-known inference algorithms for Datalog. They have much in common, which manifests in them sharing many underlying definitions (e.g., in `Eval/Candidates.lean` for traversing program rules).

**`Stepwise.lean`** is perhaps the simplest to understand, because it stays close to our formulation of the semantics: one step at a time, try to find one (grounded) rule to apply, building up the model one atom in each step.

```
∅ ──────▸ {a} ──────▸ {a,b} ──────▸ {a,b,c} ──▸ ⋯
    +a         +b           +c
```

**`Layerwise.lean`** is a second evaluator that we include. It implements a textbook algorithm often called "naive evaluation", applying every gound rule that is applicable in parallel, in rounds, to a fixed point.

### Incremental Mode

Given command line parameter `-i` or `--interactive`, the interpreter starts in interactive mode.
It will read the input line by line, discarding malformed lines, and (re)computing the model of the program given so far.

### Correctness

Conceptually, there are several correctness criteria for a Datalog interpreter:
1. never output an atom not in the program's model
2. never omit an atom in the program's model from the output
3. terminate (never get stuck working when a correct output exists)

Mechanically, these are formulated in (the definitions underneath) the aforementioned `Evaluator`:
1. `saturate` is a total function of the program (hence, terminating), and
2. for each program, prove that the output is precisely a model, as it is defined in the semantics.

Thus, for example, we prove that every conceivable evaluator agrees on every input program's model.

```lean
theorem Evaluator.agree (e₁ e₂: Evaluator) (p: Program):
    ((· ∈ e₁.saturate p): Kb) = ((· ∈ e₂.saturate p): Kb)
:= p.model_unique (e₁.model p) (e₂.model p)
```

To be convinced of correctness, a skeptical reader can work backwards from the entrypoint (`main` in `Main.lean`). Try `#print axioms` to confirm that no difficulties are smuggled under the rug behind unacceptable axioms; we use only a few standard, sound axioms such as `propext` (propositional extensionality) whose contribution boils away as Lean compiles the binary.

### Benchmarking

The evaluators we include are optimised for simplicitly, not runtime speed.
Nevertheless, we have included a second source entrypoint and compilation target for benchmarking the speed of our interpreter using either of our evaluators head-to-head.

We do this for two reasons:
1. it showcases that evaluators that necessarily compute the same models can nevertheless work at different speeds.
2. it affords users a secondary method of understanding each evaluator.

`Bench.lean` times our two evaluators on a suite of test programs, and prints their absolute and relative runtimes in a table.
This shows how our behaviourally equivalent evaluators differ in speed.

Of course, the runtime depends on your platform, so tests do not pass or fail; their runtimes are just reported.

```sh
lake exe bench          # ~2s
lake exe bench 2000     # raise the per-cell budget, in ms
```

The benchmarking instrumentation is hardcoded in Lean, but the test programs are not.
Instead, they are read from the `benchmark` directory.
Try adding your own!
Precisely, each test program is the concatenation of two parts, one from `benchmark/data`, and the other from `benchmark/rules`. The idea is roughly that different data shows how the runtime scales for the same rules.

