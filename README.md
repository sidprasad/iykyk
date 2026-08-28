# iykyk

[![CI](https://github.com/sidprasad/iykyk/actions/workflows/ci.yml/badge.svg)](https://github.com/sidprasad/iykyk/actions/workflows/ci.yml)

`iykyk` is a semantic extraction layer for Lean proof contexts. It turns what Lean knows about a
selected term into a finite program object that other tools can inspect, without changing the
caller's proof state. The object is proof-backed: its facts carry Lean proof terms, and its combined
certificate can be checked by Lean's kernel.


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
  [0] edge source (Classical.choose route)
  [1] edge (Classical.choose route) target
certificate: ∃ w0, edge source w0 ∧ edge w0 target
status: complete
```

The same choice term appears in both facts, so the shared identity of the unknown middle vertex is
preserved. Each `KnownFact` contains the proposition and a proof term checked at insertion time.

The `certificate` line is the whole result as one proposition — the design document's `⟦K⟧ₜ`: the
facts conjoined, with each shared witness abstracted back into a single existential binder. On
every extraction, its one combined proof is checked by `Lean.Kernel.check` (the kernel itself, not
the elaborator) in the captured local context. So the central contract, that the context entails
everything the extractor reports, is not a claim about the implementation being bug-free; it is
re-established by the kernel on each run.

## Lightweight hooks

The extraction policy stays small, but callers can opt into familiar Lean tools:

```lean
-- Apply an explicit forward rule.
iykyk source using [step]

-- Treat suitable raw proof hypotheses as forward rules.
iykyk source using *

-- Let any established rule-shaped fact fire in later rounds.
iykyk source using facts

-- Normalize established facts with Lean's standard simp set and simprocs.
iykyk source with [simp]

-- Use only the listed simp rules, without the global simp set or default simprocs.
iykyk source with [simp only [reverse]]

-- Ask Aesop to prove one proposition worth exposing.
iykyk source deriving [Reachable source] with [aesop]

-- Clauses compose and may appear in any order.
iykyk source using [step] deriving [Reachable source] with [simp, aesop]
```

Plain `iykyk source` does not apply implication hypotheses as rules and does not invoke `simp` or
Aesop. Each extension is explicit:

- `using [rules]` applies exactly the listed forward rules, with an `Iff` firing in both directions;
- `using *` also selects suitable raw proof hypotheses from the local context as rules;
- `using facts` lets every established rule-shaped fact fire, including implications exposed by
  conjunction or equivalence decomposition. This subsumes `using *` and runs to a bounded fixed
  point, so newly derived rules may fire in later rounds;
- `deriving` names propositions the caller cares about; an unproved candidate is simply omitted
  and remains unknown; and
- `with` selects proof-producing engines.

The engine-specific choices are explicit too:

- `simp` uses Lean's standard simp theorems and default simprocs while transporting proofs and can
  discharge named candidates;
- `simp only [rules]` uses just those rules (plus Lean's reflexivity builtins), with neither the
  global simp set nor default simprocs; and
- `aesop` performs bounded search for named candidates and for `False` when checking consistency.

These are hooks, not a second automation language. iykyk still decides what its public knowledge
object contains, preserves witnesses, applies the configured bounds, and projects to the selected
root. A result from either engine crosses the boundary only as a Lean proof term, which is checked
against the proposition before the fact is admitted. `using facts` needs repeated rounds because a
round may establish both a new rule and a premise for it; `maxRounds` and `maxFacts` keep that search
finite, and `truncated` reports when a bound stopped it — that is, when extraction ended without
reaching a fixpoint. Disjunctive resolution is exempt from the round budget: it can only expose
branches of disjunctions already present, never invent new terms, so it runs to a local fixpoint
within a single round and a chain of dependent resolutions costs one round however long it is. Provenance would explain why each fact was
found, but it is not part of the trust boundary: the proof term and final kernel-checked certificate
establish that the reported fact is true.

## Formal metatheory

The formal model lives separately in [`metatheory/`](./metatheory). It defines contexts as sets of
possible worlds and proves three kinds of results, each falsifiable:

- **Soundness.** `Derivation` is a syntactic calculus over hypothesis facts — membership,
  conjunction and equivalence elimination, disjunctive syllogism, universal instantiation, forward
  application — with no rule that accepts an unchecked semantic certificate. `Derivation.sound`
  proves every rule preserves entailment; `extract_sound` extends this to knowledge values whose
  remaining facts carry certificates.
- **Losslessness.** `entails_and_iff`, `entails_equivalence_iff`, and
  `exists_shared_witness_iff` prove that conjunction splitting, equivalence directions, and
  shared-witness existential decomposition preserve exactly the information of the hypothesis they
  decompose. `Formula.decompose_sound` and `Formula.decompose_lossless` verify the pure recursive
  decomposition algorithm for nested atoms, conjunctions, and existentials.
  Soundness alone would be satisfied by reporting nothing; these are the properties the trivial
  extractor fails.
- **Counterexamples.** `unshared_witnesses_lossy` proves that splitting an existential into facts
  about unrelated witnesses loses information, and `branch_choice_unsound` proves that reporting
  one branch of a disjunction is unsound. The two central design decisions are forced, not
  aesthetic.

The runtime is connected to this model in two enforced ways, documented in
[`metatheory/README.md`](./metatheory/README.md): `RootedKnowledge` has a private constructor, so
the only ways to build one are checked smart constructors that mirror the proved
`CertifiedKnowledge` operations one for one; and each extraction result's reified certificate is
checked by the kernel per run. The deliberately trusted remainder is interpreting a kernel-checked
`Expr` as a semantic statement; formalizing Lean's kernel in Lean is out of scope (and a reflection
principle for it is impossible internally).

## What works

- conjunction splitting and shared existential witnesses;
- reuse of an in-scope existential witness when its structural facts are already known;
- decomposition of an equivalence into its two checked implication directions;
- explicit forward rules, raw-local-rule discovery, and bounded established-fact saturation;
- opt-in standard `simp`, restricted `simp only`, and bounded Aesop candidate proving;
- bounded inference with a distinct `truncated` status;
- preservation of disjunctions without choosing a branch, plus checked disjunctive syllogism;
- direct inconsistency detection, with broader proof search when Aesop is selected;
- projection to the connected component containing the selected root;
- an unforgeable `RootedKnowledge`: private constructors, so facts and witnesses enter only through
  checked smart constructors mirroring the metatheory's certified operations;
- per-run kernel certification: the result is reified into one existentially quantified
  conjunction whose proof `Lean.Kernel.check` verifies in the captured scope (see
  `Iykyk/Certify.lean`, on by default, `kernelCheck := false` to disable); and
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
| Proof-producing automation / proof-carrying code | `Iykyk/Automation.lean`, `Iykyk/Certify.lean` | Keep automation behind a checked certificate boundary; let the kernel re-check the result. |
| LCF-style kernels | `Iykyk/Knowledge.lean` | Make certified values unforgeable outside a small checked interface. |
| Possible-world semantics / refinement invariants | `metatheory/IykykMetatheory.lean` | State and prove the extraction soundness contract. |
| Typed holes / live programming | `Iykyk/Tactic.lean` | Expose useful semantics while a proof is in progress. |

Full citations and the broader research framing remain in [DESIGN.md](./DESIGN.md).

## Build and examples

```sh
lake build
lake env lean Iykyk/Examples/Graph.lean
lake env lean Iykyk/Examples/Bounded.lean
lake env lean Iykyk/Examples/Automation.lean
lake env lean Iykyk/Examples/Certified.lean
```

The project uses Lean 4.33.1 and pins Aesop 4.33.0 (plus its Batteries dependency) through Lake.
