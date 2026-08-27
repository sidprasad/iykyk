# iykyk

`iykyk` extracts finite, proof-backed knowledge about a selected Lean term from the current proof
context. It is an early prototype of the design in [DESIGN.md](./DESIGN.md).

```lean
import Iykyk

variable {Vertex : Type}
variable (edge : Vertex → Vertex → Prop)

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  iykyk source
  trivial
```

The tactic reports:

```text
root: source
witnesses:
  •0 : Vertex := Classical.choose route
facts:
  edge source (Classical.choose route)
  edge (Classical.choose route) target
status: complete
```

The same choice term appears in both facts, so the shared identity of the unknown middle vertex is
preserved. Each `KnownFact` contains the proposition and a proof term checked by Lean.

## Lightweight hooks

The extraction policy stays small, but callers can opt into familiar Lean tools:

```lean
-- Apply an explicit forward rule.
iykyk source using [step]

-- Normalize established facts with simp.
iykyk source with [simp]

-- Ask Aesop to prove one proposition worth exposing.
iykyk source deriving [Reachable source] with [aesop]

-- Clauses compose and may appear in any order.
iykyk source using [step] deriving [Reachable source] with [simp, aesop]
```

`using` tells iykyk how to extend its finite forward search. `deriving` names propositions the
caller cares about; an unproved candidate is simply omitted and remains unknown. `with` selects
proof-producing engines:

- `simp` transports proofs while normalizing established facts and can discharge named candidates;
- `aesop` performs bounded search for named candidates and for `False` when checking consistency.

These are hooks, not a second automation language. iykyk still decides what its public knowledge
object contains, preserves witnesses, applies the configured bounds, and projects to the selected
root. A result from either engine crosses the boundary only as a Lean proof term, which is checked
against the proposition before the fact is admitted.

## What works

- conjunction splitting and shared existential witnesses;
- explicitly supplied Horn-style forward rules with `iykyk root using [rule₁, rule₂]`;
- opt-in `simp` normalization and bounded Aesop candidate proving;
- bounded inference with a distinct `truncated` status;
- preservation of disjunctions without choosing a branch;
- direct inconsistency detection, with broader proof search when Aesop is selected;
- projection to the connected component containing the selected root; and
- a programmatic `Iykyk.extract` API plus consumer-neutral queries in `Iykyk.Query`.

The first representation is intentionally small. It stores Lean `Expr`s and proof terms in their
captured `LocalContext`; stable `Classical.choose` terms avoid adding witness free variables. More
aggressive equality normalization, constructor inference, and branch-sensitive knowledge remain
future work.

## Academic lineage

Academic influences are flagged in the module comment of the file where each idea matters:

| Idea | Implementation file | Design insight |
| --- | --- | --- |
| Incomplete relational databases | `Iykyk/Knowledge.lean` | Preserve unknown identity; omission is not falsity. |
| Constraint programming | `Iykyk/Query.lean` | Query accumulated constraints before values are complete. |
| Database chase | `Iykyk/Extract.lean` | Make forward rounds and their bounds explicit. |
| Abstract interpretation / shape analysis | `Iykyk/Extract.lean` | Return a sound finite view and report truncation separately. |
| Proof-producing automation / proof-carrying code | `Iykyk/Automation.lean` | Keep automation behind a checked certificate boundary. |
| Typed holes / live programming | `Iykyk/Tactic.lean` | Expose useful semantics while a proof is in progress. |

Full citations and the broader research framing remain in [DESIGN.md](./DESIGN.md).

## Build and examples

```sh
lake build
lake env lean Iykyk/Examples/Graph.lean
lake env lean Iykyk/Examples/Bounded.lean
lake env lean Iykyk/Examples/Automation.lean
```

The project uses Lean 4.33.1 and pins Aesop 4.33.0 (plus its Batteries dependency) through Lake.
