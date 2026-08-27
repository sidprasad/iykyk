# Extracting Partial Values from Proof Contexts

## Thesis

A Lean context does more than list hypotheses. It describes what is currently
known about the values in scope. This project extracts that knowledge into an
ordinary, proof-backed object before any consumer decides how to query,
visualize, compare, or serialize it.

The selected value may not be computable or fully determined. Extraction is
still useful because a context can establish some of its structure and
relations. Missing information remains missing. Every fact that does appear is
accompanied by a Lean proof.

## A motivating example

Consider the middle of a graph-theory proof:

```lean
variable {Vertex : Type}
variable (edge : Vertex → Vertex → Prop)

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  -- What do we know about `source` here?
  trivial
```

There is no concrete graph to evaluate, and the context does not identify the
middle vertex. It nevertheless establishes a small, useful piece of graph:

```text
root: source
witness: middle
facts:
  edge source middle
  edge middle target
```

The identity of `middle` matters. The two edge facts refer to the same unknown
vertex. Replacing it with two unrelated placeholders would lose knowledge;
inventing a concrete vertex would add knowledge that the proof does not have.

This result is not a proof-state display. It does not show the goal, tactic
state, or syntax of `route`. It is a finite description of `source` and its
known surroundings, extracted from the proof state. A graph viewer could draw
it, a query tool could inspect it, and another tactic could compare it with the
knowledge available later in the proof.

## The object of study

Let `Γ` be a Lean context and `t` a selected term. A valuation `ρ` satisfies
`Γ` when it assigns values to the variables in the context in a way that makes
all of its assumptions true. Each satisfying valuation gives one possible
meaning to `t`.

We can therefore read `(Γ, t)` as a family of possible completions:

\[
  \operatorname{Completions}(\Gamma,t)
  = \{(\rho,\llbracket t\rrbracket_\rho) \mid \rho \models \Gamma\}.
\]

The valuation remains in this definition because knowledge about `t` can
involve other values in its surroundings. In the graph example, knowing only
the set of possible values of `source` would discard the path through the
shared witness.

The extractor computes a finite account `K` of facts common to every permitted
completion. Its central contract is:

\[
  \operatorname{extract}(\Gamma,t)=K
  \quad\Longrightarrow\quad
  \Gamma \models \llbracket K\rrbracket_t.
\]

Here `⟦K⟧ₜ` is the proposition expressed by the extracted knowledge when `t`
is treated as its root. The contract concerns the meaning of `K`, not its
eventual presentation. It says that every completion allowed by `Γ` agrees
with every fact in `K`.

This is a soundness claim, not a completeness claim. The extractor may omit a
fact because it is irrelevant to the root, because the configured search was
bounded, or because the implementation does not know how to derive it. An
omitted fact is unknown; it is never interpreted as false.

## Why not construct a partial Lean value?

For some inductive values, a context may determine enough constructor fields to
suggest a value containing holes. That is a useful special case, but it is too
narrow to define the library boundary.

First, knowledge can cross the boundary of the selected value's type. A value
of type `Vertex` has no field in which to store the proposition that it has an
edge to another vertex. Second, the context may determine a relation without
determining either participant. The shared `middle` vertex in the graph example
must remain one unknown used in two places. Third, the context may rule out
possibilities without choosing a constructor from which a Lean term can be
built. Finally, Lean metavariables are obligations to solve inside an
elaboration process; they are not a durable public representation of partial
information for arbitrary consumers.

The core result should therefore be knowledge *about* a value, with the value
marked as its root. A consumer may reconstruct a partial constructor tree when
the facts justify one, just as Spytial may construct a relational data instance
when its vocabulary matches the facts. Neither observation is the definition
of extraction.

## The extracted value

The initial library should expose a `RootedKnowledge` value with three semantic
ingredients:

1. a distinguished root corresponding to `t`;
2. named or scoped unknowns whose identities can be shared across facts; and
3. normalized facts, each carrying evidence accepted by Lean.

A fourth, operational field may report that bounded inference stopped before
reaching a fixed point. This status is information about extraction, not a fact
about the selected value.

The precise Lean representation is an implementation question, but the public
shape should be close to the following:

```lean
structure KnownFact where
  proposition : Expr
  proof : Expr

structure Witness where
  id : WitnessId
  type : Expr

structure RootedKnowledge where
  root : Expr
  witnesses : Array Witness
  facts : Array KnownFact
  truncated : Bool
```

This sketch leaves an important detail open: a proof mentioning an existential
witness is valid inside the scope in which that witness was introduced. The
implementation must represent that scope faithfully, rather than pretending
that every fact is independently closed. One option is to produce a single
certificate for an existentially quantified conjunction and expose projections
through a typed interface. Another is to retain a scoped proof context in the
knowledge object. The choice should be settled by a small prototype.

`RootedKnowledge` is intentionally not a Spytial `DataInstance`. It does not
choose atoms, relation names, labels, JSON fields, or drawing rules. Those are
observations that a consumer may make of the extracted knowledge.

## Extraction

Extraction starts with facts already present in the local context and grows a
small body of knowledge about the root. Every operation must construct proof
evidence at the moment it adds a fact.

The first useful operations are:

- split conjunctions and expose existential witnesses while preserving their
  shared identity and scope;
- normalize equalities and local definitions;
- apply a bounded set of explicitly supplied forward rules;
- infer constructor shape when a proof excludes the other constructors;
- retain facts connected to the selected root; and
- project away facts or witnesses that a consumer did not request.

These operations are small enough to certify directly. For example, adding a
fact requires a proof of that fact; deleting a fact preserves soundness;
strengthening the context preserves an existing certificate; and applying a
forward rule uses the proof of the rule together with proofs of its premises.

Constructor inference is more involved but follows the same rule. If a fact
about a tree's depth rules out the leaf constructor, the extractor must build a
Lean proof by cases on the tree, derive a contradiction in the leaf case, and
return witnesses for the node fields. If it cannot build that proof, the node
does not appear in the result.

The engine is deliberately bounded. A rule such as

```lean
seed : Reach start
step : ∀ x, Reach x → Reach (next x)
```

can derive facts forever. The extractor should return a certified finite
prefix and mark the result as truncated. Proof checking answers whether the
prefix is true; the status answers whether search stopped early. These are
separate questions.

Disjunction also exposes the difference between truth and useful shared
knowledge. From `P a ∨ Q a`, the extractor may not choose either branch. It may
retain the disjunction as a fact or compute facts justified in both branches,
but it must not present `P a` or `Q a` unconditionally. Branch-sensitive
knowledge is a possible later extension, not a requirement for the first
prototype.

## Why a small extraction engine?

Lean's automation remains useful for proving individual obligations, but it
does not by itself define the extracted object. The library needs predictable
rules for which facts become public, how existential witnesses are shared, how
far inference proceeds, and how relevance to the root is determined.

A small forward engine makes those choices explicit. It can ask `simp`,
`aesop`, or other procedures to discharge a generated proposition, but a fact
enters `RootedKnowledge` only when the engine obtains a proof term. This keeps
the contract stable even if the proving strategy changes.

The prototype exposes this as a few ordinary tactic clauses rather than a new
automation language:

```lean
iykyk source using [step]
iykyk source with [simp]
iykyk source deriving [Reachable source] with [aesop]
```

Here `simp` can normalize established facts, while `simp` and Aesop can try to
prove caller-named candidates. Aesop may also search for a contradiction. These
are explicitly selected, bounded hooks. They can improve which true facts the
extractor finds, but they do not change the representation, relevance policy,
or certification boundary.

The certificate is therefore an enforcement mechanism, not the main research
claim. It prevents a bug or heuristic from silently turning a plausible fact
into reported knowledge. The more important contribution is the extracted
object and the boundary it creates between proof-context reasoning and its many
possible uses.

## Consumer boundary

Consumers receive `RootedKnowledge` and decide how to observe it. A consumer
may ignore facts, rename entities for presentation, or translate a selected
vocabulary into its own data model. It must not claim that a derived observation
contains more information than the certified knowledge supports.

Spytial is one such consumer:

```text
(proof context Γ, selected term t)
                 │
                 ▼
       Lean Knowledge extraction
                 │
                 ▼
          RootedKnowledge K
                 │
                 ▼
    Spytial relational observation
                 │
                 ▼
             DataInstance
                 │
                 ▼
              diagram
```

The boundary of this project is the production of `K`. Spytial may translate
`K` into atoms and relations, then apply its existing visualization pipeline.
Nothing in the extraction contract refers to a rendered diagram or to JSON
serialization.

Other consumers could support semantic queries, show how knowledge changes
between proof steps, explain the inputs available to automation, or provide a
structured interface for external tools. These uses need not agree on one
relational vocabulary or presentation.

## Cases that define the boundary

The prototype should include small literate examples whose expected results are
easy to inspect.

### Shared existential witness

```lean
route : ∃ middle, edge source middle ∧ edge middle target
```

The result contains two edges joined by one unknown vertex. This is the central
example because it demonstrates information that cannot be represented by
merely returning a partially filled value of type `Vertex`.

### Derived knowledge

```lean
route : ∃ middle, edge source middle ∧ edge middle target
step  : ∀ x y, edge x y → Reach x y
```

If forward application is enabled for `step`, any reported `Reach` fact must
carry the proof obtained by applying `step` to an edge proof.

### Productive rule

```lean
seed : Reach start
step : ∀ x, Reach x → Reach (next x)
```

The result is a finite certified prefix with `truncated = true`. The term
`next x` may need a fresh display identity such as `•₁` in a consumer, but that
presentation choice does not belong in the core object.

### Disjunction

```lean
choice : edge source left ∨ edge source right
```

Neither edge is an unconditional fact. The extractor preserves the disjunction
or returns only consequences common to both cases.

### Inconsistent context

If `Γ` is inconsistent, classical entailment makes every proposition true. A
tool that displayed arbitrary facts in this case would be technically sound and
practically useless. The first implementation should detect a proved
contradiction and return a distinct inconsistent result rather than fabricate a
maximal `RootedKnowledge` value.

## What this project does not claim

This project does not visualize proof states, reconstruct a complete value,
enumerate all models of a context, or compete with general theorem proving. It
does not promise completeness. It does not require every consumer to use
relational data. It also does not claim that certification is novel on its own;
Lean already checks proof terms. The design contribution is to make partial
knowledge about a selected value an explicit, reusable program object.

## Research framing

### Context

Programming environments increasingly work with artifacts before they are
fully determined. Typed holes, proof goals, partial programs, generated code,
and symbolic execution all leave useful semantic information in the surrounding
environment. Most tools either wait for a concrete value or expose the state of
the reasoning process itself.

### Inquiry

How can a programming environment expose a value when the value is constrained
but incomplete? In Lean, the immediate question is how to turn a context `Γ`
and selected term `t` into finite ordinary data that records what every
completion of the context agrees upon.

### Approach

We treat `(Γ, t)` as a family of pointed completions and extract a rooted body
of facts shared by those completions. Existential witnesses preserve identity
across facts, inference is explicitly bounded, and each reported fact is
accepted only with a Lean proof. Presentation is delegated to consumers.

### Knowledge

The central object is a partial value understood through program knowledge. It
is neither a missing concrete value nor a proof state. It is a finite,
inspectable account of guaranteed structure and relations, including shared
unknowns, with absence interpreted as lack of knowledge rather than falsity.

### Grounding

A Lean prototype can ground the idea at two levels. Its formal contract states
that the meaning of extracted knowledge follows from the current context. Its
literate examples exercise existential sharing, proof-producing inference,
constructor reasoning, disjunction, inconsistency, and bounded productive
rules. Lean's kernel checks the evidence attached to every reported fact.

### Importance

Once partial knowledge is ordinary data, it can support more than one interface.
Spytial can visualize it, query tools can search it, proof environments can
compare it across steps, and external tools can consume it without interpreting
Lean's whole tactic state. The abstraction lets these systems share one account
of what is known while choosing different presentations and interactions.

## Intellectual lineage

The design sits between several established ideas:

- incomplete relational databases describe possible completions while
  preserving the identity of unknown values;
- logic and functional-logic programming use variables and unification as data
  is progressively constrained;
- the database chase makes rule-driven witness introduction explicit;
- abstract interpretation and shape analysis compute sound, incomplete views
  of program states; and
- typed-hole and live-programming systems expose useful meaning before a
  program is complete.

The proposed object differs in emphasis. It is rooted at a selected Lean term,
uses a proof context as its source of knowledge, carries kernel-checkable
evidence, and is designed as a reusable library boundary rather than a single
visual interface.

Useful starting references include Imieliński and Lipski on
[incomplete information in relational databases](https://www.inf.unibz.it/~nutt/Teaching/FDBs1718/FDBsPapers/imielinskiLipski-JACM-84.pdf),
Saraswat and Rinard on
[concurrent constraint programming](https://doi.org/10.1145/96709.96733),
Fagin et al. on
[data exchange and the chase](https://doi.org/10.1016/j.tcs.2004.10.002),
Sagiv, Reps, and Wilhelm on
[parametric shape analysis](https://doi.org/10.1145/514188.514190), and
Omar et al. on
[live functional programming with typed holes](https://doi.org/10.1145/3290327).

## Questions for the prototype

The first implementation should answer a small number of design questions:

1. Should normalized facts remain Lean expressions, or should the library use a
   typed intermediate language with an interpretation back into Lean?
2. How should existential scopes be represented so that consumers can inspect
   shared witnesses without handling unsafe free variables?
3. Which facts count as connected to the root, and should relevance be part of
   extraction or an independent projection operation?
4. Which inference rules belong in the core, and which should be supplied by a
   caller?
5. What is the smallest consumer interface that can translate knowledge without
   coupling the core library to Spytial's relational model?

The prototype succeeds if the graph examples produce small inspectable values,
every included fact is checked by Lean, and a second consumer can use the same
result without depending on Spytial.
