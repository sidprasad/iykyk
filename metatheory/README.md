# Metatheory boundary

`IykykMetatheory.lean` formalizes the semantic contract without modeling Lean internals: contexts
are predicates selecting possible worlds, and facts are predicates that must hold in every selected
world. The development is arranged so that each theorem is falsifiable — it says something a wrong
design or a wrong implementation would violate.

## What is proved

**Soundness of the calculus.** `Derivation hyps fact` is a syntactic calculus over a list of
hypothesis facts. Its only base rule is membership in the hypotheses; there is no constructor that
accepts a bare semantic entailment. `Derivation.sound` proves that every rule the extractor uses —
hypothesis lookup, conjunction elimination, universal instantiation, forward application —
preserves entailment. Adding an unsound rule (say, projecting one branch of a disjunction) would
make this theorem unprovable, which is the property the earlier draft lacked: its `certificate`
constructor admitted any entailment, making soundness a tautology.

**Losslessness of decomposition.** Soundness alone is satisfied by an extractor that reports
nothing, so the metatheory also states what decomposition preserves. `entails_and_iff` proves that
the two components of a conjunction are jointly exactly as strong as the conjunction.
`exists_shared_witness_iff` proves the same for existentials decomposed through one shared witness:
the witness facts reassemble into the original existential. These are the properties that
distinguish the real extractor from the trivial one.

**Counterexamples for the rejected designs.** Two tempting simplifications are proved wrong of
concrete contexts, so the design decisions they justify are forced rather than aesthetic:

- `unshared_witnesses_lossy` — splitting an existential into facts about two unrelated witnesses
  loses information: each component can be separately witnessed while the shared existential is
  false.
- `branch_choice_unsound` — reporting one branch of a disjunction is unsound: a consistent context
  can entail a disjunction and neither disjunct.

**The certified-knowledge API.** `CertifiedKnowledge` proves that the empty value is sound, that
adding a fact requires a certificate, and that projection, truncation, and context strengthening
preserve soundness. Inconsistency is kept a separate result because it entails every fact
(`inconsistent_entails`).

## Correspondence with the implementation

Each runtime operation is the image of exactly one proved operation or theorem:

| Runtime (`Iykyk/…`) | Metatheory |
| --- | --- |
| hypothesis collection (`collectContext`) | `Derivation.hyp` |
| `And.left` / `And.right` splitting | `Derivation.andLeft` / `andRight`, `entails_and_iff` |
| rule instantiation and application (`applyRule`) | `Derivation.instantiate`, `Derivation.forward` |
| existential decomposition via `Classical.choose` | `exists_shared_witness_iff` |
| engine-proved candidate (`proveCandidate`) | the certificate disjunct of `extract_sound` |
| `RootedKnowledge.empty` / `addFact` | `CertifiedKnowledge.empty` / `add` |
| `RootedKnowledge.project` (`projectToRoot`) | `CertifiedKnowledge.project` |
| `RootedKnowledge.withTruncated` | `CertifiedKnowledge.withTruncated` |
| distinct `Inconsistency` result | `inconsistent_entails`, `CertifiedResult` |
| witness terms shared across facts | `unshared_witnesses_lossy` (why sharing is required) |
| disjunctions kept whole | `branch_choice_unsound` (why choosing is forbidden) |

The correspondence is enforced structurally, not just documented: `RootedKnowledge` and
`Inconsistency` have private constructors, so the checked smart constructors in
`Iykyk/Knowledge.lean` — which mirror the `CertifiedKnowledge` operations — are the only way to
build one.

## The trusted bridge

The operational extractor works with `Lean.Expr`, `LocalContext`, and `MetaM`. Three layers connect
it to the semantics, in increasing strength:

1. every fact and witness is checked against its evidence at insertion time (elaborator-level
   definitional equality, `checkEvidence`);
2. every finished extraction result is reified into a single certificate — the design document's
   `⟦K⟧ₜ`, an existentially quantified conjunction in which each shared witness is one binder — and
   that certificate is checked by `Lean.Kernel.check`, the kernel itself, in the captured scope
   (`Iykyk/Certify.lean`); and
3. CI re-checks the compiled environment with an independent kernel pass and audits axioms.

What remains trusted is the reading of a kernel-checked `Expr` as a statement about possible
worlds. That step cannot be internalized: it would require formalizing Lean's type theory in Lean
and a reflection principle ("kernel-accepted implies true") that implies Lean's own consistency.
The project therefore follows the standard architecture of proof-producing automation: the
metaprogram is untrusted, and every run's output carries evidence the kernel checks.
