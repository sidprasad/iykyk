# iykyk: Semantic Extraction from Lean Proof Contexts


`iykyk` is a semantic extraction layer for Lean proof contexts. Given a local context `Γ` and a
selected term `t`, it produces a finite program object describing facts that `Γ` establishes about
`t` and its known surroundings. The object preserves the identity of existentially known values,
distinguishes missing knowledge from falsehood, reports bounded search explicitly, and carries Lean
proof terms for every fact. Extraction reads the context without changing the caller's proof state,
and a combined certificate for the result is checked by Lean's kernel.

Lean already contains all of the essential proof mechanisms used here. `rcases` can expose an
existential witness, `choose` can name one, `simp` can normalize propositions, Aesop can search for
proofs, the metaprogramming API exposes the local context, and the kernel checks proof terms. `iykyk`
does not replace or improve those mechanisms as theorem-proving procedures.

Instead,

The contribution is an abstraction boundary: standard Lean operations are composed into a
root-focused, proof-backed, explicitly incomplete semantic snapshot. A tactic normally leaves its
result distributed across a changed proof state. iykyk is an idempotent observation of that state:
it records selected consequences as one value without consuming the hypotheses it observes. The
value can also express extraction-level outcomes—such as truncation or deliberate refusal to
display arbitrary consequences of an inconsistent context—that are not themselves hypotheses in
`Γ`. The novelty claim is therefore architectural rather than foundational: witness extraction,
proof search, and kernel checking are existing ingredients; their organization into this
particular reusable object is the proposal being evaluated.

## The Problem

A Lean proof context is usually presented as a list of local declarations followed by a goal:

```text
source target : Vertex
route : ∃ middle, edge source middle ∧ edge middle target
⊢ True
```

This view is useful for continuing the proof (?), but does not directly answer semantic inspection
questions like:

> What does this context tell me about `source`?

The answer is not merely the syntax of `route`. The context establishes a small graph fragment:

```text
root: source
witness: middle
facts:
  edge source middle
  edge middle target
```

- The `middle` vertex is not (whats the right word here? concrete), but it is necessary if one were to []...]
- Replacing it with two unrelated placeholders loses information; inventing a concrete
vertex adds information the proof does not contain.

- Nor is the answer a partially constructed `Vertex`. The interesting knowledge crosses the type
boundary of the selected term: `edge source middle` is a relation, not a field of `source`.
- A useful representation must therefore describe guaranteed structure and relations around a value, not only
attempt to reconstruct the value itself.

This distinction appears throughout interactive programming. A value may be incomplete while its
surrounding constraints already determine useful properties. The immediate design question is how
to make those properties ordinary, finite, inspectable data without claiming more than Lean has
proved.

## Lean already provides the mechanical bits we need.

The design starts from a skeptical position: Lean can already expose everything in
the example above.

### 2.1 `rcases` and existential elimination

`rcases`' recursive pattern language is a convenient way to open existentials, conjunctions, structures, and alternatives.
A proof author can write:

```lean
example (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  rcases route with ⟨middle, sourceToMiddle, middleToTarget⟩
  -- middle          : Vertex
  -- sourceToMiddle  : edge source middle
  -- middleToTarget  : edge middle target
  trivial
```

Here, `rcases` restructures the proof state. It applies the relevant eliminators and introduces fresh
local declarations for the components of the selected hypothesis. 

- While very convenient, this state transition is why `rcases` is not a great tool for observation or inspection. 
- It consumes the selected occurrence of `route` while replacing it with the components; running the same command a
second time does not perform the same read. 
- Asking “what did the context know about `source` here,
and what did it know three tactics ago?” should not require rewriting the proof at either point.

**Semantic inspection needs a non-interfering read whose result can be retained and compared.**

This is not a competing notion of semantic extraction. It is one of the mechanisms iykyk can use.
The implementation currently constructs the term-level equivalent:

```lean
let middle := Classical.choose route
have body : edge source middle ∧ edge middle target := Classical.choose_spec route
have sourceToMiddle : edge source middle := body.left
have middleToTarget : edge middle target := body.right
```

In `Iykyk/Extract.lean`, these operations are built as `Expr`s using `Classical.choose`,
`Classical.choose_spec`, `And.left`, and `And.right`. Both edge facts therefore contain the same
choice term.

The reason to use these terms instead of literally executing `rcases` is representational, not
logical. `rcases` introduces a fresh local variable in an extended proof context. Such a free
variable cannot escape that scope unless the result remains under its binder or is abstracted over
it. `Classical.choose route` is already a term in the original context, so it can occur directly in
stored fact expressions. During final certification, iykyk abstracts the choice term back into one
existential binder.


### 2.2 `choose`

At term level, `Exists.choose h` selects a witness for `h : ∃ x, P x`, while
`Exists.choose_spec h` proves the predicate for that witness. Mathlib's `choose` tactic supplies a
convenient proof-state interface and also supports Skolemization, for example turning

```lean
h : ∀ x, ∃ y, R x y
```

into a choice function and its specification.

iykyk does not obtain witnesses that `choose` cannot obtain. It directly constructs the underlying
terms because it needs control over how witness identity appears in the stored expressions. Since
`Exists` lives in `Prop`, a classical chosen witness is generally noncomputable: it is a symbolic
Lean term for proof and metaprogramming, not executable data recovered from an erased proof.

### 2.3 `simp` and other automation

`simp` is proof-producing normalization, so iykyk exposes it as a small opt-in hook. Aesop is
proof-producing but goal-directed; without caller-selected goals, it does not yet have a precise
inspection-wide role and is therefore deferred.

Neither engine by itself specifies a semantic snapshot. A proof procedure answers questions such
as “can this goal be transformed?” or “can this candidate proposition be proved?” It does not
decide which term is the root of an extracted object, how existential identities appear across
facts, which established facts are relevant, when an incomplete search is returned, or what public
representation records the answer.

### 2.4 The metaprogramming API and proof-state interfaces

Lean's `LocalContext` API provides the raw declarations needed to build iykyk. Proof-state displays
render those declarations for humans. Libraries such as ProofWidgets support custom and
domain-specific presentations.

These are lower- and upper-level interfaces around the proposed boundary. A `LocalContext` is raw
input: each caller still has to decide how to decompose propositions, preserve scope, and select
relevant consequences. Running `rcases` and then reading the new hypotheses exposes the syntax the
proof author chose to produce; it does not compute the semantic neighborhood of a selected term.
`projectToRoot` instead computes a connected component through established fact arguments.

A local context also has no declaration representing “this bounded observation was truncated” or
“`Γ` is contradictory, so the extractor is deliberately returning no ordinary knowledge.” Those
are properties of the extraction process. They exist in iykyk because extraction returns an
`WdykResult`, rather than pretending that every meaningful outcome must be another local
hypothesis. A widget is presentation: it still needs some account of the meaning to display. iykyk
proposes the small semantic object between raw declarations and presentation.

### 2.5 Summary of the comparison

| Existing mechanism | What it already solves | What iykyk uses it for |
| --- | --- | --- |
| `cases`, `rcases`, `obtain` | Decompose a selected hypothesis by changing the proof state | The model for safe structural decomposition, used without exposing mutation as the API |
| `Exists.choose`, mathlib `choose` | Select witnesses and prove their specifications | Stable symbolic witness terms shared across facts |
| `simp` | Normalize propositions while transporting proofs | Optional fact normalization through `via` |
| Aesop | Search for proofs under a rule policy | Deferred until inspection defines finite obligations |
| `LocalContext` / `MetaM` | Inspect the current syntactic declarations and construct expressions | Raw input from which root projection and extraction status are computed |
| Lean's kernel | Check proof terms | Per-run validation of the combined result |

If the task is to open one existential and continue a proof, direct tactics are simpler. iykyk is
not justified by witness access alone.

## 3 What's The Claim?

A finite proof-backed account of what a Lean context knows about a value is a useful program object in its own right.

The project tests that thesis by combining eight properties in one interface:

1. **Observation.** Extraction does not consume hypotheses, transform the goal, or require the
   proof to be reorganized for inspection. Repeating the same extraction in the same state is the
   same semantic read.
2. **Rootedness.** The result is centered on a selected term rather than being an undifferentiated
   dump of the proof state.
3. **Relational partial knowledge.** Facts may describe relations around the root, not only a
   partially reconstructed value of its type.
4. **Shared unknown identity.** One existential witness remains one unknown wherever it occurs.
5. **Proof-backed content.** Each fact carries evidence, and the whole snapshot has a combined
   certificate.
6. **Explicit incompleteness.** Missing facts remain unknown, and bounded search reports
   truncation separately from truth.
7. **Extraction-level status.** Truncation and inconsistency are represented as outcomes of
   observation rather than encoded as spurious propositions about the root.
8. **Policy separation.** The snapshot contract does not depend on whether a fact was found by
   direct decomposition, forward rules, `simp`, Aesop, or a future proof-producing engine.


Systems that export or control proof
states, such as LeanDojo and Pantograph, solve a broader machine-interaction problem and primarily
represent goals, tactics, premises, and proof transitions. iykyk instead performs an in-process
semantic **projection** of one current context around one selected term.

The distinction must remain falsifiable. If the object is not useful beyond its first integration,
if raw `LocalContext` traversal is just as simple for each use, or if the representation cannot
remain stable across proving engines, then the abstraction has not earned its cost.

## More formally 

Let `Γ` be a Lean local context and `t` a well-scoped selected term. A valuation `ρ` satisfies `Γ`
when it assigns values to the variables in the context in a way that makes all assumptions true.
Each satisfying valuation gives one possible meaning to `t`.

We read `(Γ, t)` as a family of pointed completions:

\[
  \operatorname{Completions}(\Gamma,t)
  = \{(\rho,\llbracket t\rrbracket_\rho) \mid \rho \models \Gamma\}.
\]

The valuation stays in this definition because knowledge about `t` can involve other values. In
the graph example, recording only possible values for `source` would discard the path through the
shared middle vertex.

Extraction computes a finite account `K` with the contract:

\[
  \operatorname{wdyk}(\Gamma,t)=K
  \quad\Longrightarrow\quad
  \Gamma \models \llbracket K\rrbracket_t.
\]

`⟦K⟧ₜ` is the proposition jointly expressed by the facts in `K`, with shared witnesses bound once.
For the running example:

\[
  \llbracket K\rrbracket_{source}
  = \exists middle,\; edge\;source\;middle \land edge\;middle\;target.
\]

This is a **soundness** (not a completeness) contract. Extraction may omit a true fact because
it is disconnected from the root, because a configured limit stopped search, or because no
implemented rule derives it.

**What about inconsistent contexts?**
Classically, an inconsistent `Γ` entails every
proposition, so returning arbitrary facts would be sound but useless. `WdykResult` therefore
distinguishes ordinary knowledge from a checked contradiction.

## 5. The extracted program object

The runtime representation is intentionally close to the following:

```lean
structure KnownFact where
  proposition : Expr
  proof : Expr

structure Witness where
  id : WitnessId
  type : Expr
  term : Expr

structure Afaik where
  root : Expr
  scope : LocalContext
  witnesses : Array Witness
  facts : Array KnownFact
  truncated : Bool

inductive WdykResult where
  | afaik (value : Afaik)
  | inconsistent (value : Inconsistency)
```

The actual constructors for `Afaik` and `Inconsistency` are private. Knowledge is created
through checked smart constructors, projected by deletion, and marked truncated without changing
its semantic content.

`WdykResult.snapshot` (`Iykyk/Snapshot.lean`) presents either result as one `Snapshot`—root,
scope, facts, witness groups, status, and certificate—which is the shape of the metatheory's
consumer contract (§8.2). A witness group pairs one witness with the indices of the facts that
mention its term.

The fields have distinct roles:

- `root` identifies the selected term;
- `scope` is the captured context in which every stored expression is meaningful;
- `witnesses` assigns stable identities to symbolic existential choices;
- `facts` stores propositions paired with proof terms; and
- `truncated` records an operational fact about search, not a proposition about the root.

The current representation is an in-process Lean metaprogramming value, not a portable
serialization format. Its `Expr`s remain meaningful in the captured `LocalContext`. A future
serialization layer would need stable names, explicit binders, and a vocabulary for declarations;
that concern is intentionally outside the initial object.

## 6. Extraction algorithm

The implementation is a small proof-producing forward engine. Given a root and configuration, it
performs the following stages.

### 6.1 Capture the context

The root is normalized, the current `LocalContext` is captured, and every non-implementation-detail
local declaration whose type is a proposition becomes an initial source of knowledge.

This stage reads the main context but does not replace its declarations or mutate the proof goal.
The extracted facts live in the returned object; they are not installed as new hypotheses for the
caller.

If `fyi *` is selected, rule-shaped facts discovered during decomposition may also participate in
forward inference. Plain extraction does not globally treat every implication as an active rule.

### 6.2 Structural decomposition

Each proved proposition is recursively decomposed using ordinary Lean proof constructors:

- `A ∧ B` produces `A` and `B` using `And.left` and `And.right`;
- `A ↔ B` produces the two implication directions using `Iff.mp` and `Iff.mpr`;
- `∃ x, P x` records one `Classical.choose` witness and decomposes
  `Classical.choose_spec`; and
- `A ∨ B` is retained without choosing a branch.

Before creating a new choice term for an existential, the extractor checks whether an in-scope
term of the right type already has the required structural facts. This avoids inventing a second
identity when the context already names a suitable witness.

Every admitted fact is normalized, deduplicated, checked against its proof, and subject to the fact
limit.

### 6.3 Forward inference

Rules come from two explicit policies:

```lean
wdyk source fyi [step]  -- exactly the listed proved hypotheses
wdyk source fyi *       -- every established rule-shaped fact
```

Explicit `Iff` rules fire in both directions. `fyi *` includes rule-shaped propositions
uncovered during decomposition, so later results can feed back into inference. This requires
repeated rounds: one round may expose a rule, a later round may prove its premise, and the new
conclusion may enable another rule.

`maxRounds` and `maxFacts` keep this process finite. A productive rule such as

```lean
seed : Reach start
step : ∀ x, Reach x → Reach (next x)
```

can otherwise generate an unbounded sequence. The returned finite prefix is still sound;
`truncated = true` reports that search stopped before a fixpoint.

### 6.4 Disjunction and inconsistency

From `A ∨ B` alone, neither branch is public knowledge. If `¬A` is also established, the extractor
may add `B` using `Or.resolve_left`; symmetrically, `¬B` permits `A`.

Resolution runs to a local fixpoint within a saturation round. It can only expose branches of
already stored disjunctions and is bounded by the fact limit, so a chain of dependent disjunctive
resolutions does not consume one global inference round per link.

A direct proof of `False` or a positive fact paired with its negation yields
`WdykResult.inconsistent` rather than an arbitrary maximal fact set.

### 6.5 Projection to the root

By default, the extractor retains the connected component containing the selected root. The
prototype builds this component by following term occurrences through proposition arguments and
then removes unused witnesses.

This is a deliberately simple relevance heuristic, not a complete semantic dependency analysis.
It makes the first object small and gives future work a concrete policy to improve or replace.

For a value focus, projection retains the connected component containing that value. For an
evidence focus such as `wdyk route`, the proposition proved by the selected term is decomposed
directly; this avoids discarding its consequences merely because propositions do not syntactically
contain their proof terms.

### 6.6 Certification

The remaining facts are conjoined in order. Every witness still appearing in them is abstracted
into one existential binder, so repeated occurrences of one choice term become structural sharing
under one binder. For the graph example the certificate is:

```lean
∃ w, edge source w ∧ edge w target
```

The combined proof is checked by `Lean.Kernel.check` in the captured local context. Certification
is enabled by default.

## 7. Relationship to `simp`

The proof engines are deliberately hooks rather than the definition of extraction:

```lean
wdyk source via [simp]
wdyk source via [simp only [reverse]]
```

Standard `simp` uses Lean's active simp theorems and default simprocs. `simp only` uses only the
listed entries, with minimal reflexivity builtins and no default simprocs.

The engine boundary is proof-producing. A result crosses it only as a proposition and proof term;
iykyk independently checks that evidence before adding the fact. Changing the search procedure can
change which facts are discovered, but it does not change what makes a `Afaik` valid.

Plain `wdyk source` does not invoke `simp`. This matters because hidden normalization would make
extraction difficult to predict. Goal-directed mechanisms instead live behind the downstream
`prove`/`prove?` query boundary, where the consumer supplies one proposition and a deterministic
heartbeat budget. The initial focused mechanisms are `simp` and Presburger arithmetic via
`omega`; neither mechanism adds its consequences back into the snapshot.

## 8. Correctness and trust

There are three related but distinct correctness stories.

### 8.1 Lean already checks proofs

Every Lean tactic ultimately constructs a term checked by Lean. iykyk does not make proof checking
novel. Its runtime contribution is to require evidence at the knowledge-object boundary:

- `addFact` checks that the supplied proof has the claimed proposition;
- `addWitness` checks that the witness term has the declared type;
- private constructors prevent callers from bypassing those checks accidentally; and
- final certification asks the kernel to check the conjunction of the whole result.

Thus a buggy search heuristic may omit facts, choose a poor ordering, or truncate too early, but it
cannot silently admit a false proposition unless it also finds a proof term accepted by the kernel
or crosses the explicitly trusted boundary.

### 8.2 What the formal metatheory proves

The separate model in `metatheory/IykykMetatheory.lean` treats contexts as sets of possible worlds
and proves five families of results:

1. **Derivation soundness.** Hypothesis lookup, conjunction and equivalence elimination,
   disjunctive syllogism, universal instantiation, and forward application preserve entailment.
2. **Decomposition soundness.** Every fact returned by the pure recursive formula decomposition is
   entailed by the input context.
3. **Decomposition losslessness.** Conjunction, equivalence, and shared-witness existential
   decomposition jointly reconstruct the information they decompose.
4. **Certified-knowledge closure.** Empty knowledge is sound; adding a certified fact, projecting,
   marking truncation, and strengthening the context preserve soundness.
5. **Snapshot contract.** The judgment `Γ ; root ⊢extract[policy] K` packages a finished
   result—root, finite checked facts, witness groups, context, and status—and its laws are
   theorems: every fact is entailed and so is the combined proposition `⟦K⟧ₜ`; each witness group
   is satisfied by one value in every compatible world; projection and truncation preserve
   soundness; an inconsistent status carries a proof; and `saturated` is not a completeness
   claim, since the judgment admits a saturated snapshot that omits an entailed fact.

Soundness alone would be satisfied by an extractor that always returned no facts. The losslessness
theorems rule out that vacuous interpretation for the structural fragment. Concrete
counterexamples also show why two tempting designs are rejected:

- splitting an existential into facts about unrelated witnesses loses information; and
- selecting one branch of a disjunction is unsound.

### 8.3 What the metatheory does not prove

The metatheory is not a formal verification of the Lean metaprogram implementation. It models the
calculus and proves its intended laws; correspondence with the runtime is maintained structurally
and tested by the checked construction API and per-run kernel certificate.

Nor can iykyk internally prove a general reflection principle saying that every kernel-accepted
Lean proposition is semantically true without formalizing an appropriate model of Lean's type
theory and accepting the associated consistency assumptions. The deliberately trusted remainder
is the standard one: Lean's kernel plus the interpretation of checked expressions as semantic
statements.

The metatheory therefore serves two purposes that kernel checking alone does not:

- it states precisely what the extracted object is intended to mean; and
- it demonstrates that witness sharing, omission-as-unknown, and non-selection of disjunctions are
  semantic requirements rather than presentation preferences.

Kernel certification remains the operational trust mechanism for each actual result.

## 9. Why the abstraction matters

The central practical problem is not that Lean hides its witnesses. It does not. The problem is
that the result of ordinary proof manipulation remains encoded as local proof-state structure and
as the sequence of tactics that produced it.

Making a semantic account explicit has several consequences.

### 9.1 Observation is not a state transition

Tactics such as `rcases` are designed to advance a proof. They consume or replace declarations and
leave later tactics in a different state. That is appropriate for proving; it is the wrong contract
for inspection.

`Iykyk.wdyk` is designed as a read. It leaves the caller's goal and hypotheses alone, so the
same observation can be requested repeatedly and observations can be placed at different proof
points without changing the proof merely to make it inspectable. This is essential for comparing
what was known before and after a sequence of tactics.

### 9.2 A semantic projection is more than a hypothesis listing

Reading the local declarations after some chosen decompositions reports a syntactic proof state.
iykyk instead recursively derives safe structural facts and projects their argument-connectivity
graph to the component rooted at the selected term.

The returned object can also state that this computation was truncated or that the source context
was inconsistent and ordinary facts are intentionally being withheld. Neither condition is a
proposition the original context needs to contain. They are metadata about how the semantic view
was obtained and how it should be interpreted.

### 9.3 Partial values become usable before computation is possible

The selected term need not reduce to a constructor or concrete datum. Relations, exclusions, and
shared existential identities may already be known. Treating that knowledge as data avoids waiting
for a value that the context may never determine.

### 9.4 Extraction policy becomes testable

Questions that are implicit in an ad hoc context traversal become explicit library behavior:

- Does conjunction split?
- Do the directions of an equivalence become rules?
- Are implication hypotheses active by default?
- Is the global simp set allowed?
- What happens when search is bounded?
- Which facts are relevant to the root?

These choices can be documented, regression-tested, and changed deliberately.

### 9.5 Proof search is separated from knowledge validity

Different mechanisms may discover different subsets of the truth. By accepting only proof-backed
facts, the knowledge contract remains stable across those discovery policies. This permits a small,
predictable default while allowing explicit normalization.

### 9.6 One context can support more than one observation

The extracted value does not choose diagram nodes, relational atoms, source labels, JSON fields, or
display syntax. Those are interpretations of the knowledge, not part of its truth conditions.

Spytial is the first concrete integration: it calls `Iykyk.wdyk`, translates selected facts and
witnesses into a relational instance, and then applies its own visualization pipeline. That
integration demonstrates that the API is usable, but one consumer is not enough to establish that
the abstraction is broadly reusable. A second materially different use would be stronger evidence.

Potential uses include semantic queries over the current context, comparison of knowledge across
proof steps, structured explanations of inputs available to automation, and machine-facing
interfaces that need more meaning than a pretty-printed goal state.

## 10. Boundary cases

Small examples define the intended semantics more clearly than broad slogans.

### Shared existential witness

```lean
route : ∃ middle, edge source middle ∧ edge middle target
```

The result contains two edges joined by one unknown vertex. It must not contain two unrelated
witnesses.

### Existing named witness

```lean
middle : Vertex
left  : edge source middle
right : edge middle target
route : ∃ w, edge source w ∧ edge w target
```

If the structural facts already establish that the named `middle` is a witness, extraction should
reuse the in-scope identity rather than introduce a second choice term.

### Derived knowledge

```lean
edgeFact : edge source target
step : ∀ x y, edge x y → Reach x y
```

With `step` enabled, any reported `Reach source target` fact must carry the proof obtained by
applying the rule to `edgeFact`.

### Productive rule

```lean
seed : Reach start
step : ∀ x, Reach x → Reach (next x)
```

Extraction returns a finite certified prefix. If the configured bounds stop before a fixpoint,
`truncated` is true.

### Disjunction

```lean
choice : edge source left ∨ edge source right
```

Neither edge is unconditional knowledge. A proved negation of one branch may resolve the other;
otherwise the disjunction remains whole.

### Inconsistent context

```lean
h : P
notH : ¬P
```

The result is an explicit inconsistency with a proof of `False`, not a collection of arbitrary
consequences.

## 11. Current scope and limitations

The prototype currently supports:

- conjunction and shared-existential decomposition;
- equivalence directions;
- preservation and checked resolution of disjunctions;
- direct contradiction detection;
- explicit hypotheses and established-fact forward saturation;
- opt-in standard `simp` and restricted `simp only`;
- root-component projection;
- bounded saturation with explicit truncation;
- checked smart constructors and per-run kernel certification; and
- a programmatic `Iykyk.wdyk` API with small consumer-neutral queries.

Important limitations remain:

- relevance is based on syntactic term connectivity rather than a formal semantic slice;
- equality normalization is limited;
- constructor-shape inference is not implemented;
- branch-sensitive conditional knowledge is not represented;
- witness scope is encoded with classical choice terms rather than an explicit telescope;
- provenance explains neither the source hypothesis nor inference path of each fact;
- the result is not stable serialized data outside its captured context;
- extraction is incomplete even when `truncated = false`—that status means the configured engine
  reached its own fixpoint, not that every logical consequence was found; and
- kernel certification currently requires a fully elaborated, metavariable-free scope and may need
  to be disabled for unsupported universe-polymorphic situations.

These limitations are compatible with the soundness contract. They determine usefulness and
predictability, not whether an admitted fact is true.

## 12. Related work

### 12.1 Lean tactics and metaprogramming

Lean's quantifier rules, `cases`/`rcases`, and term-level choice already provide witness access.
Mathlib's `choose` tactic provides Skolemization. These mechanisms act on a selected hypothesis or
construct selected terms; iykyk composes the same operations across a context and records the
result.

Lean's simplifier, Omega, and Aesop are proof-producing automation. The extraction-time `via`
boundary exposes only simplification, whose input is the finite set of already established facts.
The downstream query boundary also exposes simplification and Omega for bounded, caller-selected
goals. Aesop remains deferred pending a comparably explicit and predictable search policy.

ProofWidgets provides infrastructure for symbolic visualizations, tactic interfaces, and
domain-specific goal displays. It addresses presentation and interaction; iykyk addresses the
semantic value that a presentation may inspect.

LeanDojo and Pantograph expose Lean proof states and interactions to external programs, especially
for automated and learned theorem proving. They make goals, tactics, premises, and proof
transitions machine-accessible. iykyk is narrower and in-process: it projects a current local
context into proved relational knowledge around one term. These approaches are complementary; an
external proof interface could transport or request an iykyk-style snapshot.

### 12.2 Incomplete information and possible worlds

Incomplete relational databases distinguish unknown values from absent or false facts and preserve
the identity of labeled unknowns across tuples. Imieliński and Lipski's possible-world treatment of
incomplete information is the closest model for the interpretation of shared witnesses and
omission-as-unknown.

iykyk differs by taking a Lean proof context as the specification of possible worlds and attaching
Lean evidence to every reported fact.

### 12.3 Constraint programming and the database chase

Constraint programming treats partially determined values as useful objects constrained by
accumulated relations. The database chase repeatedly applies dependencies, introduces witnesses,
and may fail to terminate without restrictions.

These traditions motivate iykyk's forward saturation, shared witness identity, explicit rule
selection, and separate truncation status. iykyk is not a general constraint solver or chase
implementation; its first engine handles a small proof-producing fragment.

### 12.4 Abstract interpretation and shape analysis

Abstract interpretation and shape analysis compute finite sound accounts of possibly unbounded
program states. They motivate the separation between soundness and completeness: a finite view may
be useful even when it omits true facts, provided its approximation direction is clear.

Unlike a fixed abstract domain, iykyk's initial fact language is Lean `Expr`, and each included fact
has a proof. A future typed intermediate language could make the abstract domain and its operations
more explicit.

### 12.5 Typed holes and live programming

Typed-hole and live-programming systems expose useful semantic feedback before a program is
complete. iykyk applies the same interaction principle to proof contexts: a selected value can have
inspectable meaning before it is concrete or the surrounding theorem is finished.

### 12.6 LCF-style kernels and proof-producing automation

LCF-style systems isolate trust in a small kernel and allow complex tactics to search outside that
trusted core. iykyk follows this pattern: extraction and automation may be heuristic, but facts
cross the boundary with proof terms and the combined result is rechecked.

This trust architecture is established practice, not a novelty claim. Its importance here is that
semantic extraction can be extended without making every search heuristic part of the trusted
base.

### 12.7 References

- Lean, [Quantifiers](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Quantifiers/)
  and [Tactic proofs](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/).
- Mathlib, [`choose` tactic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Choose.html).
- Jannis Limperg and Asta Halkjær From,
  [*Aesop: White-Box Best-First Proof Search for Lean*](https://doi.org/10.1145/3573105.3575671).
- Wojciech Nawrocki and E. W. Ayers,
  [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4).
- Kaiyu Yang et al.,
  [*LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*](https://arxiv.org/abs/2306.15626).
- Leni Aniva et al.,
  [*Pantograph: A Machine-to-Machine Interaction Interface for Advanced Theorem Proving, High
  Level Reasoning, and Data Extraction in Lean 4*](https://doi.org/10.1007/978-3-031-90643-5_6).
- Tomasz Imieliński and Witold Lipski,
  [*Incomplete Information in Relational Databases*](https://www.inf.unibz.it/~nutt/Teaching/FDBs1718/FDBsPapers/imielinskiLipski-JACM-84.pdf).
- Vijay Saraswat and Martin Rinard,
  [*Concurrent Constraint Programming*](https://doi.org/10.1145/96709.96733).
- Ronald Fagin et al.,
  [*Data Exchange: Semantics and Query Answering*](https://doi.org/10.1016/j.tcs.2004.10.002).
- Mooly Sagiv, Thomas Reps, and Reinhard Wilhelm,
  [*Parametric Shape Analysis via 3-Valued Logic*](https://doi.org/10.1145/514188.514190).
- Cyrus Omar et al.,
  [*Live Functional Programming with Typed Holes*](https://doi.org/10.1145/3290327).

## 13. Command vocabulary and implementation plan

The package keeps the name **iykyk**. The primary operation is `wdyk`, read as “what do you
know about this expression?” Its result is an **Afaik**: an “as far as I know” value whose reported
facts are proved, whose omissions are not claims of falsity, and whose saturation status says only
whether this configured finite extraction reached a fixpoint.

These names belong to the programmatic abstraction, not only its tactic frontend. The intended
public boundary reads like this:

```lean
match ← Iykyk.wdyk subject { hypotheses := #[step], mechanisms := #[.simp] } with
| .afaik view => Spytial.relationalizeAfaik view
| .inconsistent contradiction => ...
```

The tactic is a human-facing frontend to that same operation:

```lean
wdyk source
wdyk source fyi [step]
wdyk source fyi *
wdyk source fyi [step] via [simp]
```

The clauses describe information flow rather than caller-selected goals:

| Command | Role | Previous surface syntax |
| --- | --- | --- |
| `wdyk focus` | Inspect finite knowledge around a selected value or evidence term | `iykyk root` |
| `fyi [hypotheses]` | Identify proved hypotheses or rules that may participate in inference | `using [rules]` |
| `fyi *` | Promote all discoverable rule-shaped knowledge and saturate | `using *`, `using facts` |
| `nvm [hypotheses]` | Exclude named local declarations from this extraction | — (new) |
| `via [mechanisms]` | Select proof-producing mechanisms; initially `simp` | `with [engines]` |

`fyi` accepts proof terms, never bare unproved propositions. Plain `wdyk` still reads ordinary
propositional locals as facts; `fyi` marks hypotheses that may be used generatively as forward
rules, and `fyi *` opts into the strongest bounded established-fact saturation policy. `via`
changes how proved information is processed, never what counts as evidence. In particular, simp
can normalize established facts while transporting their proofs.

`nvm [hypotheses]` is the one subtractive clause. It names local declarations by `FVarId`, and the
extractor skips them during context collection, so their decomposed facts and witnesses never enter
the knowledge. An excluded declaration therefore forms no relevance bridge and takes no part in
forward saturation, contradiction detection, or downstream queries for that one extraction. This is
narrower than the Lean-level workaround `clear h`: exclusion changes only what a single `wdyk`
observes, never the caller's proof state, so a rule-shaped hypothesis needed later in the proof can
still be omitted from an inspection that would otherwise inherit an unwanted connection. Because
identity is by declaration rather than by structural equality of the proposition, an excluded
hypothesis and an unrelated proof of the same statement are distinguished. Exclusion is defined to
take precedence over `fyi`: a declaration named in both clauses is dropped, keeping the guarantee
that a name in `nvm` plays no part in the extraction. The lower-level `Config.excludedHypotheses`
field carries the same set for programmatic callers such as Spytial, which controls which certified
knowledge is extracted rather than how a consumer renders it.

Aesop is not included initially. It is goal directed and cannot enumerate arbitrary consequences;
without caller-selected goals, inspection does not define a principled finite set of Aesop
obligations. `via` on extraction currently supports `simp` and `simp only`. Downstream
`prove`/`prove?` queries accept caller-selected goals and support focused `simp` and `omega`
mechanisms without modifying the extracted `Afaik`.

The existing `deriving [propositions]` clause is removed, not renamed. It asks simp or Aesop to
prove caller-selected goals and then inserts successful results into the snapshot. That is useful
proof-assistant automation, but it is not part of the inspection abstraction. Particular
entailment queries belong to downstream consumers of `Afaik`. No `lmk`, `checking`, or `wdym`
command is included in this migration; a second command should be introduced only when a distinct
programmatic operation and consumer justify it.

### 13.1 Tagged implementation issues

Every implementation issue for this change carries one or more of the command tags below.
The tags identify the user-facing concept affected, even when most of the work is in shared parser,
configuration, rendering, or test code. This plan is now implemented; it remains here as the
rationale and release checklist:

- **`[wdyk]` Shared public operation.** Introduce `Iykyk.wdyk` as the programmatic operation and
  make the `wdyk` tactic a renderer over it. Keep the `Iykyk` namespace and package name. Update
  Spytial and other consumers to call this operation rather than preserving `extract` as the
  primary public vocabulary.
- **`[wdyk]` Afaik result.** Replace the former knowledge/result vocabulary with an `Afaik` view
  and a `WdykResult` that distinguishes `.afaik` from `.inconsistent`. Preserve the
  private checked-construction boundary, witness sharing, captured scope, certificate, and
  truncation flag. Prefer `saturated` over `complete` in rendered status text, since reaching an
  extraction fixpoint is not logical completeness.
- **`[wdyk]` Evidence focus.** Ensure the selected expression can be either a value, as in
  `wdyk source`, or a proof term, as in `wdyk route`. Evidence-focused extraction decomposes the
  selected proof directly rather than applying value-oriented term-connectivity projection.
- **`[fyi]` Explicit evidence.** Replace `using [rules]` with `fyi [hypotheses]`. Preserve the
  checked-evidence boundary: every entry must elaborate to a proof of a proposition. Listing an
  implication or equivalence permits it to fire as a forward rule; no entry may be interpreted as
  an unproved assumption.
- **`[fyi]` Context-wide inference.** Replace the public distinction between `using *` and
  `using facts` with `fyi *`, using the stronger established-fact saturation semantics. The lower
  level `Config` may retain separate controls for integrations that need them, but the
  conversational tactic should not expose raw-local versus subsequently established rules as two
  nearly synonymous modes.
- **`[via]` Proof-producing mechanisms.** Replace the former engine clause with `via [simp]`,
  including `via [simp only [...]]`. Simp continues to normalize established facts. Defer Aesop
  until finite inspection-generated obligations are specified. Diagnostics use the new vocabulary
  and remain attached to the offending syntax.
- **`[wdyk] [via]` Remove goal-directed candidates.** Delete the `deriving` grammar, candidate
  configuration, candidate-proving pass, examples, and documentation. Keep downstream lookup of
  propositions in an `Afaik`; do not replace candidate proving with another tactic clause.
- **`[wdyk] [fyi] [via]` Compatibility policy.** Coordinate the programmatic rename with Spytial.
  If the old API has not been released as stable, replace it directly and update both repositories
  together. Otherwise retain old spellings for one documented deprecation cycle, elaborating them
  to the same implementation rather than maintaining two paths.
- **`[wdyk] [fyi] [via]` Documentation and tests.** Give each command or clause at least one
  positive example and one misuse example where applicable, and pin its report or diagnostic
  contract. README examples should lead with the conversational reading; implementation terms
  such as engines and saturation belong in the detailed explanation that follows.

The implementation is complete when the new examples compile, all report and error text uses the new
vocabulary, Spytial consumes the new programmatic API, candidate proving is gone, and a
repository-wide search finds old spellings only in an intentional compatibility section. The
public abstraction and surface language change together; the kernel-checked knowledge contract
does not.

## 14. Evaluation and next questions

The prototype should be judged on more than compilation. Evidence for the abstraction would
include:

1. **Semantic examples.** Shared witnesses, disjunctions, inconsistency, equivalences, and bounded
   productive rules behave as specified.
2. **Trust tests.** Forged facts and mismatched witnesses are rejected, while every normal result
   produces a kernel-accepted combined certificate.
3. **Predictability.** Defaults remain small; every broader inference source and proof engine is
   explicit; truncation is visible.
4. **Reuse.** At least two materially different integrations consume `Afaik` without
   importing each other's vocabulary.
5. **Stability.** Improving or replacing proof search does not require changing the validity
   contract of the extracted value.
6. **Explanatory value.** The object is meaningfully easier to query or translate than raw local
   declarations for its intended tasks.

The next design questions are:

- Should witnesses move from choice terms to an explicit scoped telescope?
- Should facts remain general `Expr`s or use a typed intermediate language with an interpretation
  back into Lean?
- Can relevance be specified and proved as a semantic slicing operation rather than a syntactic
  connectivity heuristic?
- Which equality and constructor inferences add substantial value without making extraction
  unpredictable?
- What provenance is sufficient to explain an extraction without becoming part of the trust
  boundary?
- Which second integration best tests whether the interface is genuinely consumer-neutral?

## 15. Non-claims

iykyk does not claim to:

- reveal witnesses unavailable to `rcases`, `choose`, or the Lean metaprogramming API;
- replace `simp`, Aesop, or general theorem proving;
- reconstruct every selected term as a concrete or partial value;
- enumerate all models or all logical consequences of a context;
- prove its own runtime implementation correct inside Lean;
- make kernel certification novel;
- provide a general proof-state UI or external interaction protocol; or
- guarantee logical completeness when its configured search reaches a fixpoint.

The project succeeds if it provides a small, trustworthy, useful answer to one question:

> Given this Lean context and this selected term, what finite body of proved knowledge should an
> ordinary program be able to inspect right now?

## Conclusion

Lean already knows how to eliminate existentials, split conjunctions, normalize propositions,
search for proofs, and check the resulting terms. iykyk does not compete with those capabilities.
It gives their relevant results a particular shape: a finite semantic snapshot rooted at a term,
with shared unknowns, proof-backed facts, explicit bounds, and a combined certificate.

That shape is the hypothesis. The implementation and metatheory make it concrete enough to test;
the examples and integrations must determine whether it is worth keeping.
