# iykyk

[![CI](https://github.com/sidprasad/iykyk/actions/workflows/ci.yml/badge.svg)](https://github.com/sidprasad/iykyk/actions/workflows/ci.yml)

`iykyk` is a semantic extraction layer for Lean proof contexts. Ask `wdyk` (“what do you know?”)
about a selected term and it returns an `Afaik`: a finite, proof-backed account of what the current
context establishes. Missing facts remain unknown rather than false, and inspection does not change
the caller's proof state.

```lean
import Iykyk

variable {Vertex : Type}
variable (edge : Vertex → Vertex → Prop)

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  wdyk source
  trivial
```

The tactic reports the shared existential witness, its two proved edge facts, a combined
kernel-checked certificate, and whether the configured finite extraction saturated:

```text
afaik
  root: source
  witnesses:
    •0 : Vertex := Classical.choose route
  facts:
    [0] edge source (Classical.choose route)
    [1] edge (Classical.choose route) target
  certificate: ∃ w0, edge source w0 ∧ edge w0 target
  status: saturated
```

The same choice term occurs in both facts, preserving the identity of the unknown middle vertex.
Each fact carries a Lean proof checked when it enters the `Afaik`; the combined certificate is then
checked by `Lean.Kernel.check` in the captured local context.

## The command language

The surface deliberately describes information flow rather than proof goals:

```lean
-- Inspect the context around a value.
wdyk source

-- A proof term is also a useful focus: inspect what this evidence establishes.
wdyk route

-- Supply proved hypotheses or forward rules that may be useful.
wdyk source fyi [step]

-- Let every established rule-shaped fact participate in bounded saturation.
wdyk source fyi *

-- Normalize established facts while transporting their proofs.
wdyk source via [simp]

-- Restrict normalization to these simp rules.
wdyk source via [simp only [reverse]]

-- Clauses compose and may appear in either order.
wdyk source via [simp] fyi [step]
```

Plain `wdyk` decomposes ordinary propositional locals but does not automatically fire implication
hypotheses as rules or run `simp`.

- `fyi [hypotheses]` accepts only proof terms. An implication or equivalence may fire as a forward
  rule; an unproved proposition is never treated as an assumption.
- `fyi *` uses rule-shaped facts discovered anywhere in the established knowledge and runs to a
  bounded fixed point.
- `via [simp]` uses Lean's active simp set and simprocs. `via [simp only [...]]` uses the listed
  rules without the global simp set or default simprocs.

There is intentionally no goal-directed `deriving` clause on `wdyk`. Asking whether a particular
proposition follows is a downstream query over an already-produced `Afaik`, not another mode of
inspection. This keeps the consumer responsible for selecting useful goals and avoids attempting
to enumerate an unbounded arithmetic closure.

`maxRounds` and `maxFacts` keep saturation finite. A `truncated` result means a bound stopped the
configured extraction before its fixpoint; `saturated` does not claim logical completeness.

## Programmatic API

The meaningful words are shared by people and consumers:

```lean
open Iykyk Lean Meta

match ← Iykyk.wdyk subject {
    hypotheses := #[step]
    mechanisms := #[.simp]
  } with
| .afaik view =>
    -- inspect view.root, view.facts, view.witnesses, or view.truncated
    pure ()
| .inconsistent contradiction =>
    -- contradiction.proof proves False in contradiction.scope
    pure ()
```

`Iykyk.Query` provides consumer-neutral lookup over `Afaik`. Spytial uses this public operation and
relationalizes the returned `Afaik`; it does not depend on the tactic renderer.

It also provides bounded, goal-directed proof queries. Exact facts need no mechanism; additional
proof search is explicitly opt-in:

```lean
match ← Iykyk.prove knowledge goal {
    mechanisms := #[.simp, .omega]
    maxHeartbeats := 20_000
  } with
| .proved fact =>
    -- fact.proposition is the requested goal and fact.proof is kernel-checked evidence
    pure ()
| .notProved =>
    -- the selected mechanisms completed without finding a proof
    pure ()
| .truncated =>
    -- the deterministic query budget was exhausted
    pure ()
```

`Iykyk.prove? knowledge goal (mechanisms := #[.simp, .omega])` is the `Option KnownFact`
convenience form. Queries run in the `Afaik`'s captured scope, use its certified facts rather than
every proposition in the ambient context, restore elaborator and metavariable state before
returning, and ask the kernel to check successful proofs by default. `omega` supports focused
Presburger arithmetic over `Nat` and `Int`; it does not saturate the snapshot with arithmetic
consequences.

## Correctness boundary

The formal model in [`metatheory/`](./metatheory) treats a context as a set of possible worlds and
proves:

- soundness of hypothesis lookup, conjunction and equivalence elimination, disjunctive syllogism,
  universal instantiation, and forward application;
- losslessness of conjunction, equivalence, and shared-witness existential decomposition; and
- counterexamples showing why existential components cannot receive unrelated witnesses and why
  a disjunction cannot be replaced by either branch.

Runtime construction mirrors those proofs. `Afaik` and `Inconsistency` have private constructors;
facts and witnesses enter only through checked smart constructors. Each finished `Afaik` is reified
as one existentially quantified conjunction and checked by the kernel. See
[`metatheory/README.md`](./metatheory/README.md) and [DESIGN.md](./DESIGN.md) for the full boundary and
research framing.

## What works

- conjunction splitting and shared existential witnesses;
- evidence-focused extraction such as `wdyk route`;
- equivalence decomposition and explicit forward rules;
- bounded established-fact saturation through `fyi *`;
- opt-in standard `simp` and restricted `simp only`;
- preservation of disjunctions plus checked disjunctive syllogism;
- direct inconsistency detection;
- projection to the connected component containing a value focus;
- an unforgeable `Afaik` and per-run kernel certification; and
- a programmatic `Iykyk.wdyk` API with consumer-neutral lookup and bounded proof queries.

The representation is intentionally small. It stores Lean `Expr`s and proof terms in a captured
`LocalContext`; stable `Classical.choose` terms preserve shared witnesses. More aggressive equality
normalization, constructor inference, branch-sensitive knowledge, provenance, and broader
proof-producing mechanisms beyond focused `simp` and Presburger arithmetic remain future work.

## Build and examples

```sh
lake build
lake env lean Iykyk/Examples/Graph.lean
lake env lean Iykyk/Examples/Bounded.lean
lake env lean Iykyk/Examples/Automation.lean
lake env lean Iykyk/Examples/Certified.lean
lake env lean Iykyk/Examples/Query.lean
```

The project uses Lean 4.33.1.
