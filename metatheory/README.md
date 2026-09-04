# Metatheory boundary

`IykykMetatheory.lean` formalizes the semantic contract without modeling Lean internals: contexts
are predicates selecting possible worlds, and facts are predicates that must hold in every selected
world. The theorems are deliberately falsifiable—they rule out incorrect extraction designs rather
than merely restating that supplied certificates are valid.

`Entails` and `Knowledge.Sound` expose their definitions through Lean's module boundary. This lets
downstream mechanizations consume a sound knowledge value one world and one fact at a time without
redefining IYKYK's semantics. It does not expose the runtime representation or weaken the checked
`Lean.Expr` boundary.

## What is proved

**Soundness of the calculus.** `Derivation hyps fact` is a syntactic calculus over hypothesis facts.
Its only base rule is membership in `hyps`; there is no constructor accepting a bare semantic
entailment. `Derivation.sound` checks hypothesis lookup, conjunction and equivalence elimination,
disjunctive syllogism, universal instantiation, and forward application. An unsound inference rule
would make this theorem unprovable.

**Sound and lossless decomposition.** `entails_and_iff`, `entails_equivalence_iff`, and
`exists_shared_witness_iff` cover one conjunction, equivalence, or existential. `Formula.decompose`
is the pure recursive algorithm for arbitrarily nested atoms, conjunctions, and world-extending
existentials. `Formula.decompose_sound` proves every reported fact follows from the context, while
`Formula.decompose_lossless` proves those facts jointly reconstruct the input formula. Existential
descendants all use one chosen witness.

**Counterexamples for rejected designs.** `unshared_witnesses_lossy` exhibits separately witnessed
components whose shared existential is false. `branch_choice_unsound` exhibits a consistent context
entailing a disjunction but neither disjunct. These results force witness sharing and forbid choosing
a branch.

**The certified-knowledge API.** `CertifiedKnowledge` proves that empty knowledge is sound, adding a
fact requires a certificate, and projection, truncation, and context strengthening preserve
soundness. Inconsistency remains a separate result because it entails every fact.

**The snapshot contract.** `Snapshot` packages a finished result for consumers: the selected root,
finite checked facts, witness groups (`WitnessGroup`: one witness and the predicates stated about
it), and a `Status` of `saturated`, `truncated`, or `inconsistent`; the context in which its terms
are meaningful is its type index. `ValidSnapshot Γ root maxFacts K` is a validity judgment: it says
which snapshots are acceptable answers about `root` in `Γ` within the fact bound. Its rules are the
runtime smart constructors—`empty`, `derive` (a `Derivation` in the calculus), `certify` (an
external certificate), `openExists` (one existential opened with one shared witness), `project`,
`withTruncated`, and `inconsistent`—and its laws are theorems about it:

1. every fact is entailed (`ValidSnapshot.sound`, `ValidSnapshot.entails`), and so is the combined
   proposition `⟦K⟧` (`ValidSnapshot.interp`), which is `False` for an inconsistent snapshot and
   the conjunction of the facts with each witness bound once otherwise;
2. for each witness group, one value satisfies all of its predicates in every compatible world
   (`ValidSnapshot.shared_witness`), and the group's facts are facts of the snapshot
   (`ValidSnapshot.witness_facts`);
3. projection and truncation preserve soundness (`Snapshot.Sound.project`,
   `Snapshot.Sound.withTruncated`); and
4. the fact bound holds (`ValidSnapshot.bounded`) and an inconsistent status carries a proof
   (`ValidSnapshot.inconsistent_certified`), while `saturated_not_complete` shows the judgment
   admits a saturated snapshot that omits an entailed fact, so no status is a completeness claim.

The judgment is not an operational semantics of `wdyk`. `certify` accepts any entailed fact,
`withTruncated` either status, and the fact bound is the only configuration it constrains, so it
does not say which facts a run finds or whether saturation really occurred. Instantiating it for
an actual run would need per-fact trace evidence, which is issue #3. `ValidSnapshot.toCertified`
connects a snapshot to `CertifiedKnowledge`. `Snapshot` mentions no atom, tuple, or rendering
concept; a consumer that relationalizes it adds its own. The `Instances` namespace works three
snapshots through the judgment—a shared existential witness, a truncated run, and an inconsistent
context—matching the runtime tests in `Iykyk/Examples/Snapshot.lean`.

## Correspondence with the implementation

| Runtime (`Iykyk/…`) | Metatheory |
| --- | --- |
| hypothesis collection (`collectContext`) | `Derivation.hyp` |
| `And.left` / `And.right` splitting | `Derivation.andLeft` / `andRight`, `entails_and_iff` |
| `Iff.mp` / `Iff.mpr` directions | `Derivation.iffForward` / `iffBackward`, `entails_equivalence_iff` |
| `Or.resolve_left` / `resolve_right` | `Derivation.resolveLeft` / `resolveRight` |
| recursive conjunction/existential splitting | `Formula.decompose`, `decompose_sound`, `decompose_lossless` |
| explicit, raw-local, or established rule application (`applyRule`) | `Derivation.instantiate`, `Derivation.forward` |
| existential decomposition via `Classical.choose` | `exists_shared_witness_iff` |
| `Afaik.empty` / `addFact` | `CertifiedKnowledge.empty` / `add` |
| `Afaik.project` (`projectToRoot`) | `CertifiedKnowledge.project` |
| `Afaik.withTruncated` | `CertifiedKnowledge.withTruncated` |
| distinct `Inconsistency` result | `inconsistent_entails`, `CertifiedResult` |
| disjunctions kept whole | `branch_choice_unsound` |
| `WdykResult.snapshot` (`Iykyk/Snapshot.lean`) | `Snapshot`, `ValidSnapshot` |
| `Snapshot.witnesses`: facts mentioning one witness term | `WitnessGroup`, `ValidSnapshot.shared_witness`, `ValidSnapshot.witness_facts` |
| `Snapshot.status` | `Status`, `ValidSnapshot.inconsistent_certified`, `saturated_not_complete` |
| `Snapshot.certificate`, kernel-checked at the boundary | `Snapshot.interp`, `ValidSnapshot.interp` |

The correspondence is structural. `Afaik` and `Inconsistency` have private constructors,
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

`Iykyk/Snapshot.lean` names this boundary where a consumer meets it. `WdykResult.snapshot` is a
view with the contract's shape, not a proof of the judgment: under the trusted reading, the
snapshot of a `wdyk` result satisfies `ValidSnapshot`, with the kernel check the snapshot performs
in its own scope as the operational form of fact soundness and one witness term occurring in
several facts as the operational form of witness sharing. `Afaik`, `Inconsistency`, and `Snapshot`
have private constructors and no `Inhabited` instance, so a consumer cannot obtain one except
through the checked path.
