# Metatheory boundary

`IykykMetatheory.lean` formalizes the semantic contract without modeling Lean internals: contexts
are predicates selecting possible worlds, and facts are predicates that must hold in every selected
world. The theorems are deliberately falsifiable—they rule out incorrect extraction designs rather
than merely restating that supplied certificates are valid.

## What is proved

**Soundness of the calculus.** `Derivation hyps fact` is a syntactic calculus over hypothesis facts.
Its only base rule is membership in `hyps`; there is no constructor accepting a bare semantic
entailment. `Derivation.sound` checks hypothesis lookup, conjunction elimination, universal
instantiation, and forward application. An unsound inference rule would make this theorem
unprovable.

**Sound and lossless decomposition.** `entails_and_iff` and `exists_shared_witness_iff` cover one
conjunction or existential. `Formula.decompose` is the pure recursive algorithm for arbitrarily
nested atoms, conjunctions, and world-extending existentials. `Formula.decompose_sound` proves every
reported fact follows from the context, while `Formula.decompose_lossless` proves those facts jointly
reconstruct the input formula. Existential descendants all use one chosen witness.

**Counterexamples for rejected designs.** `unshared_witnesses_lossy` exhibits separately witnessed
components whose shared existential is false. `branch_choice_unsound` exhibits a consistent context
entailing a disjunction but neither disjunct. These results force witness sharing and forbid choosing
a branch.

**The certified-knowledge API.** `CertifiedKnowledge` proves that empty knowledge is sound, adding a
fact requires a certificate, and projection, truncation, and context strengthening preserve
soundness. Inconsistency remains a separate result because it entails every fact.

## Correspondence with the implementation

| Runtime (`Iykyk/…`) | Metatheory |
| --- | --- |
| hypothesis collection (`collectContext`) | `Derivation.hyp` |
| `And.left` / `And.right` splitting | `Derivation.andLeft` / `andRight`, `entails_and_iff` |
| recursive conjunction/existential splitting | `Formula.decompose`, `decompose_sound`, `decompose_lossless` |
| rule instantiation and application (`applyRule`) | `Derivation.instantiate`, `Derivation.forward` |
| existential decomposition via `Classical.choose` | `exists_shared_witness_iff` |
| engine-proved candidate (`proveCandidate`) | certificate disjunct of `extract_sound` |
| `RootedKnowledge.empty` / `addFact` | `CertifiedKnowledge.empty` / `add` |
| `RootedKnowledge.project` (`projectToRoot`) | `CertifiedKnowledge.project` |
| `RootedKnowledge.withTruncated` | `CertifiedKnowledge.withTruncated` |
| distinct `Inconsistency` result | `inconsistent_entails`, `CertifiedResult` |
| disjunctions kept whole | `branch_choice_unsound` |

The correspondence is structural. `RootedKnowledge` and `Inconsistency` have private constructors,
so the checked smart constructors in `Iykyk/Knowledge.lean` are the only construction path. Every
finished result is then reified into one proposition: its facts are conjoined and each shared witness
becomes one existential binder. `Iykyk/Certify.lean` checks the combined proof with
`Lean.Kernel.check` in the captured local context.

## The trusted boundary

What remains trusted is reading a kernel-checked `Expr` as a statement about possible worlds.
Internalizing that step would require formalizing Lean's type theory and adding a reflection
principle—“kernel-accepted implies true”—strong enough to imply Lean's own consistency. iykyk follows
the standard proof-producing automation boundary: metaprograms may search however they like, but
every reported result carries evidence checked by the kernel.
