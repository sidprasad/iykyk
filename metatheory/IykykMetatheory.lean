module

public import Lean

public section

/-!
# Metatheory for iykyk

This module gives the semantic core independently of Lean's `Expr` representation. A context is a
set of possible worlds, a fact is a predicate on worlds, and knowledge is sound when every reported
fact holds in every world allowed by the context.

The development is arranged so that each theorem says something an implementation could get wrong:

* `Derivation` is a syntactic calculus over a list of hypothesis facts. Its only base rule is
  membership in the hypotheses; there is no constructor that accepts a bare semantic entailment.
  `Derivation.sound` therefore checks the exact inference rules used by the extractor.
* `entails_and_iff` and `exists_shared_witness_iff` say that one-step decomposition is lossless.
  `Formula.decompose_sound` and `Formula.decompose_lossless` extend that result to nested atoms,
  conjunctions, and existentials through a pure decomposition function.
* `unshared_witnesses_lossy` and `branch_choice_unsound` refute two tempting simpler designs:
  unrelated existential witnesses and unconditional choice of a disjunctive branch.
* `CertifiedKnowledge` is the API contract mirrored by the runtime smart constructors: facts enter
  only with an entailment certificate, and projection and truncation cannot invalidate soundness.
* `Snapshot` and the validity judgment `ValidSnapshot` package a finished result for consumers:
  root, finite checked facts, witness groups, context, and status. The judgment says which
  snapshots are acceptable, not which one a run computes; its laws are theorems about it, and
  `saturated_not_complete` shows status is not completeness.

The operational extractor works with `Lean.Expr`, `LocalContext`, and `MetaM`. The bridge between
the two layers is documented in `metatheory/README.md`; its runtime half is the kernel-checked
certificate produced for every extraction result.
-/

namespace Iykyk.Metatheory

universe u v

/-- A context selects the possible worlds compatible with the current assumptions. -/
abbrev Context (World : Type u) := World → Prop

/-- A semantic fact is a predicate on possible worlds. -/
abbrev Fact (World : Type u) := World → Prop

/-- `Γ` entails `fact` when the fact holds in every world admitted by `Γ`. -/
@[expose] def Entails (Γ : Context World) (fact : Fact World) : Prop :=
  ∀ world, Γ world → fact world

/-- The context described by a list of hypothesis facts: every listed fact holds. -/
def Context.ofFacts (hyps : List (Fact World)) : Context World :=
  fun world => ∀ fact ∈ hyps, fact world

/-- Semantic knowledge about a distinguished root. -/
structure Knowledge (World : Type u) (Root : Type v) where
  root : World → Root
  facts : List (Fact World)
  truncated : Bool := false

/-- Every fact in a knowledge value follows from its context. -/
@[expose] def Knowledge.Sound (Γ : Context World) (knowledge : Knowledge World Root) : Prop :=
  ∀ {fact}, fact ∈ knowledge.facts → Entails Γ fact

/-!
## The derivation calculus

`Derivation hyps fact` says that `fact` follows from the hypothesis list by the extractor's
inference rules alone. The base rule is membership; everything else is one of the proof-producing
steps the runtime engine performs. There is deliberately no rule for choosing a disjunctive branch
and no rule that accepts an unchecked semantic certificate.
-/

/-- The proof-producing inference fragment used by the extractor, relative to named hypotheses. -/
inductive Derivation {World : Type u} (hyps : List (Fact World)) : Fact World → Prop where
  /-- A hypothesis of the context may be reported as a fact. -/
  | hyp {fact : Fact World} (mem : fact ∈ hyps) : Derivation hyps fact
  /-- Conjunction elimination, left component. -/
  | andLeft {left right : Fact World}
      (proof : Derivation hyps (fun world => left world ∧ right world)) :
      Derivation hyps left
  /-- Conjunction elimination, right component. -/
  | andRight {left right : Fact World}
      (proof : Derivation hyps (fun world => left world ∧ right world)) :
      Derivation hyps right
  /-- Forward direction of a derived equivalence. -/
  | iffForward {left right : Fact World}
      (proof : Derivation hyps (fun world => left world ↔ right world)) :
      Derivation hyps (fun world => left world → right world)
  /-- Backward direction of a derived equivalence. -/
  | iffBackward {left right : Fact World}
      (proof : Derivation hyps (fun world => left world ↔ right world)) :
      Derivation hyps (fun world => right world → left world)
  /-- Resolve the left branch of a disjunction using a derived negation. -/
  | resolveLeft {left right : Fact World}
      (choice : Derivation hyps (fun world => left world ∨ right world))
      (negative : Derivation hyps (fun world => left world → False)) :
      Derivation hyps right
  /-- Resolve the right branch of a disjunction using a derived negation. -/
  | resolveRight {left right : Fact World}
      (choice : Derivation hyps (fun world => left world ∨ right world))
      (negative : Derivation hyps (fun world => right world → False)) :
      Derivation hyps left
  /-- Instantiation of a universally quantified rule at a chosen value. -/
  | instantiate {α : Sort v} {predicate : World → α → Prop} (value : α)
      (proof : Derivation hyps (fun world => ∀ x, predicate world x)) :
      Derivation hyps (fun world => predicate world value)
  /-- Forward application of a derived implication to a derived premise. -/
  | forward {premise conclusion : Fact World}
      (premiseProof : Derivation hyps premise)
      (ruleProof : Derivation hyps (fun world => premise world → conclusion world)) :
      Derivation hyps conclusion

/--
Every derivable fact is entailed by the hypotheses. This is the load-bearing soundness theorem:
because `Derivation` has no semantic escape hatch, each constructor must be checked here, and a
constructor that reported un-entailed facts would make the theorem unprovable.
-/
theorem Derivation.sound {hyps : List (Fact World)} {fact : Fact World} :
    Derivation hyps fact → Entails (Context.ofFacts hyps) fact
  | .hyp mem => fun _ compatible => compatible _ mem
  | .andLeft proof => fun world compatible => (proof.sound world compatible).1
  | .andRight proof => fun world compatible => (proof.sound world compatible).2
  | .iffForward proof => fun world compatible => (proof.sound world compatible).mp
  | .iffBackward proof => fun world compatible => (proof.sound world compatible).mpr
  | .resolveLeft choice negative => fun world compatible =>
      (choice.sound world compatible).resolve_left (negative.sound world compatible)
  | .resolveRight choice negative => fun world compatible =>
      (choice.sound world compatible).resolve_right (negative.sound world compatible)
  | .instantiate value proof => fun world compatible => proof.sound world compatible value
  | .forward premiseProof ruleProof => fun world compatible =>
      ruleProof.sound world compatible (premiseProof.sound world compatible)

/-- Derivations transfer to any context that entails each hypothesis. -/
theorem Derivation.sound_of {Γ : Context World} {hyps : List (Fact World)} {fact : Fact World}
    (hypsHold : ∀ fact ∈ hyps, Entails Γ fact) (derivation : Derivation hyps fact) :
    Entails Γ fact :=
  fun world compatible =>
    derivation.sound world (fun hyp mem => hypsHold hyp mem world compatible)

/--
Abstract extractor soundness. Facts are admitted through exactly two doors: a derivation in the
calculus, or an external certificate of entailment. The runtime counterpart of the second door is a
proof term checked by Lean's kernel.
-/
theorem wdyk_sound {Γ : Context World} {hyps : List (Fact World)}
    {knowledge : Knowledge World Root}
    (hypsHold : ∀ fact ∈ hyps, Entails Γ fact)
    (generated : ∀ {fact}, fact ∈ knowledge.facts →
      Derivation hyps fact ∨ Entails Γ fact) :
    knowledge.Sound Γ := by
  intro fact present
  rcases generated present with derivation | certificate
  · exact derivation.sound_of hypsHold
  · exact certificate

/-!
## Losslessness

Soundness alone is satisfied by an extractor that reports nothing. The next results say that the
core decomposition steps also lose nothing: the decomposed facts jointly carry exactly the
information of the hypothesis they came from.
-/

/-- Conjunction decomposition is lossless: the two components together are the conjunction. -/
theorem entails_and_iff {Γ : Context World} {left right : Fact World} :
    Entails Γ (fun world => left world ∧ right world) ↔
      (Entails Γ left ∧ Entails Γ right) := by
  constructor
  · intro proof
    exact ⟨fun world compatible => (proof world compatible).1,
      fun world compatible => (proof world compatible).2⟩
  · intro ⟨leftProof, rightProof⟩ world compatible
    exact ⟨leftProof world compatible, rightProof world compatible⟩

/-- Equivalence decomposition is lossless: its two implication directions reconstruct it. -/
theorem entails_equivalence_iff {Γ : Context World} {left right : Fact World} :
    Entails Γ (fun world => left world ↔ right world) ↔
      (Entails Γ (fun world => left world → right world) ∧
        Entails Γ (fun world => right world → left world)) := by
  constructor
  · intro proof
    exact ⟨fun world compatible => (proof world compatible).mp,
      fun world compatible => (proof world compatible).mpr⟩
  · intro ⟨forward, backward⟩ world compatible
    exact ⟨forward world compatible, backward world compatible⟩

/-- One existential proof supplies a single witness shared by both projected facts. -/
def WitnessSatisfies (Γ : Context World) (witness : ∀ world, Γ world → α)
    (predicate : World → α → Prop) : Prop :=
  ∀ world compatible, predicate world (witness world compatible)

/-- Existential decomposition preserves witness identity across conjunction components. -/
theorem exists_shared_witness {Γ : Context World} {left right : World → α → Prop}
    (proof : Entails Γ (fun world => ∃ value, left world value ∧ right world value)) :
    ∃ witness : ∀ world, Γ world → α,
      WitnessSatisfies Γ witness left ∧ WitnessSatisfies Γ witness right := by
  let witness := fun world compatible => Classical.choose (proof world compatible)
  refine ⟨witness, ?_, ?_⟩
  · intro world compatible
    exact (Classical.choose_spec (proof world compatible)).1
  · intro world compatible
    exact (Classical.choose_spec (proof world compatible)).2

/-- Facts about one shared witness reassemble into the original existential. -/
theorem shared_witness_entails {Γ : Context World} {left right : World → α → Prop}
    {witness : ∀ world, Γ world → α}
    (leftSat : WitnessSatisfies Γ witness left)
    (rightSat : WitnessSatisfies Γ witness right) :
    Entails Γ (fun world => ∃ value, left world value ∧ right world value) :=
  fun world compatible =>
    ⟨witness world compatible, leftSat world compatible, rightSat world compatible⟩

/--
Existential decomposition through one shared witness is lossless: the pair of witness facts is
exactly as strong as the existential hypothesis they decompose.
-/
theorem exists_shared_witness_iff {Γ : Context World} {left right : World → α → Prop} :
    Entails Γ (fun world => ∃ value, left world value ∧ right world value) ↔
      ∃ witness : ∀ world, Γ world → α,
        WitnessSatisfies Γ witness left ∧ WitnessSatisfies Γ witness right := by
  constructor
  · exact exists_shared_witness
  · intro ⟨_, leftSat, rightSat⟩
    exact shared_witness_entails leftSat rightSat

/-!
## The verified decomposition core

The two iff-lemmas above cover one conjunction or one existential. `Formula` covers the whole
structural fragment the engine decomposes: atoms, conjunction, and existentials in any nesting.
An existential does not bind a variable; it extends the world, so `Formula` needs no variables,
substitution, or environments. `Formula.decompose` is the decomposition algorithm itself, written
as a pure function: conjunctions split, and an existential contributes one chosen witness shared
by every fact beneath it, exactly as the runtime engine uses one `Classical.choose` term.

`decompose_sound` says every reported fact is entailed. `decompose_lossless` says the reported
facts jointly reconstruct the hypothesis at any world whatsoever, which is only possible because
the witness is shared; `unshared_witnesses_lossy` below shows it fails otherwise.
-/

/-- The structural fragment: atoms, conjunction, and world-extending existentials. -/
inductive Formula : Type u → Type (u + 1) where
  | atom {World : Type u} (fact : Fact World) : Formula World
  | conj {World : Type u} (left right : Formula World) : Formula World
  | ex {α World : Type u} (body : Formula (α × World)) : Formula World

/-- A formula denotes one fact; an existential quantifies the world extension. -/
def Formula.interp : {World : Type u} → Formula World → Fact World
  | _, .atom fact => fact
  | _, .conj left right => fun world => left.interp world ∧ right.interp world
  | _, .ex body => fun world => ∃ value, body.interp (value, world)

/--
Decomposition: split conjunctions, and open each existential with one chosen witness that all
facts beneath it share. Beneath an existential the context is extended with the witness component.
-/
noncomputable def Formula.decompose : {World : Type u} → (Γ : Context World) →
    (f : Formula World) → Entails Γ f.interp → List (Fact World)
  | _, _, .atom fact, _ => [fact]
  | _, Γ, .conj left right, h =>
      decompose Γ left (fun world hw => (h world hw).1) ++
        decompose Γ right (fun world hw => (h world hw).2)
  | _, Γ, .ex body, h =>
      let witness := fun world hw => Classical.choose (h world hw)
      (decompose (fun p => Γ p.2 ∧ body.interp p) body (fun _ hp => hp.2)).map
        fun fact world => ∃ hw : Γ world, fact (witness world hw, world)

/-- Every fact reported by decomposition is entailed by the context. -/
theorem Formula.decompose_sound : {World : Type u} → {Γ : Context World} →
    (f : Formula World) → (h : Entails Γ f.interp) →
    ∀ fact ∈ f.decompose Γ h, Entails Γ fact
  | _, _, .atom _, h, _, mem => by
      simp only [decompose, List.mem_singleton] at mem
      exact mem ▸ h
  | _, _, .conj left right, h, _, mem => by
      rcases List.mem_append.mp mem with mem | mem
      · exact left.decompose_sound _ _ mem
      · exact right.decompose_sound _ _ mem
  | _, _, .ex body, h, _, mem => by
      simp only [decompose, List.mem_map] at mem
      obtain ⟨fact, memFact, rfl⟩ := mem
      intro world hw
      exact ⟨hw, body.decompose_sound _ fact memFact
        (Classical.choose (h world hw), world) ⟨hw, Classical.choose_spec (h world hw)⟩⟩

/-- Decomposition is nonempty: every formula contributes at least one fact. -/
theorem Formula.decompose_ne_nil : {World : Type u} → {Γ : Context World} →
    (f : Formula World) → (h : Entails Γ f.interp) → f.decompose Γ h ≠ []
  | _, _, .atom _, _ => by simp [decompose]
  | _, _, .conj left right, h => by
      intro empty
      simp only [decompose] at empty
      exact left.decompose_ne_nil _ (List.append_eq_nil_iff.mp empty).1
  | _, _, .ex body, h => by
      intro empty
      simp only [decompose, List.map_eq_nil_iff] at empty
      exact body.decompose_ne_nil _ empty

/--
The reported facts jointly reconstruct the decomposed hypothesis at any world, with no reference
to the context. Sharing is what makes this provable: each existential is re-witnessed by the one
value all of its facts constrain.
-/
theorem Formula.decompose_lossless : {World : Type u} → {Γ : Context World} →
    (f : Formula World) → (h : Entails Γ f.interp) → ∀ world,
    (∀ fact ∈ f.decompose Γ h, fact world) → f.interp world
  | _, _, .atom fact, _, world, holds => holds fact (by simp [decompose])
  | _, _, .conj left right, h, world, holds =>
      ⟨left.decompose_lossless _ world fun fact mem =>
          holds fact (List.mem_append.mpr (.inl mem)),
        right.decompose_lossless _ world fun fact mem =>
          holds fact (List.mem_append.mpr (.inr mem))⟩
  | _, Γ, .ex body, h, world, holds => by
      simp only [decompose, List.mem_map] at holds
      have entails : Entails (fun p => Γ p.2 ∧ body.interp p) body.interp := fun _ hp => hp.2
      obtain ⟨first, memFirst⟩ :=
        List.exists_mem_of_ne_nil _ (body.decompose_ne_nil entails)
      obtain ⟨hw, -⟩ := holds _ ⟨first, memFirst, rfl⟩
      show ∃ value, body.interp (value, world)
      refine ⟨Classical.choose (h world hw),
        body.decompose_lossless entails (Classical.choose (h world hw), world)
          fun fact mem => ?_⟩
      obtain ⟨hw', factHolds⟩ := holds _ ⟨fact, mem, rfl⟩
      exact factHolds

/-!
## Counterexamples for the rejected designs

Two simpler designs look plausible and are refuted by concrete contexts. These theorems are the
reason the extractor preserves witness identity and never commits to a disjunctive branch.
-/

/--
Splitting an existential into facts about two unrelated witnesses loses information: there is a
consistent context in which each component is separately witnessed, yet the shared existential is
false. So an extractor that dropped witness sharing could not reconstruct its own input.
-/
theorem unshared_witnesses_lossy :
    ∃ (World : Type) (Γ : Context World) (left right : World → Bool → Prop),
      (∃ world, Γ world) ∧
      (∃ witness : ∀ world, Γ world → Bool, WitnessSatisfies Γ witness left) ∧
      (∃ witness : ∀ world, Γ world → Bool, WitnessSatisfies Γ witness right) ∧
      ¬ Entails Γ (fun world => ∃ value, left world value ∧ right world value) := by
  refine ⟨Unit, fun _ => True, fun _ value => value = true, fun _ value => value = false,
    ⟨(), trivial⟩, ⟨fun _ _ => true, fun _ _ => rfl⟩,
    ⟨fun _ _ => false, fun _ _ => rfl⟩, ?_⟩
  intro entails
  obtain ⟨value, isTrue, isFalse⟩ := entails () trivial
  exact Bool.noConfusion (isTrue ▸ isFalse)

/--
Committing to one branch of a disjunction is unsound: there is a consistent context entailing a
disjunction but neither disjunct. So a `Derivation` rule projecting a branch would falsify
`Derivation.sound`.
-/
theorem branch_choice_unsound :
    ∃ (World : Type) (Γ : Context World) (left right : Fact World),
      (∃ world, Γ world) ∧
      Entails Γ (fun world => left world ∨ right world) ∧
      ¬ Entails Γ left ∧ ¬ Entails Γ right := by
  refine ⟨Bool, fun _ => True, fun world => world = true, fun world => world = false,
    ⟨true, trivial⟩, ?_, ?_, ?_⟩
  · intro world _
    cases world
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro entails
    exact Bool.noConfusion (entails false trivial)
  · intro entails
    exact Bool.noConfusion (entails true trivial)

/-- A consequence proved in both branches may be reported without choosing a branch. -/
theorem common_of_disjunction {Γ : Context World} {left right result : Fact World}
    (choice : Entails Γ (fun world => left world ∨ right world))
    (fromLeft : Entails Γ (fun world => left world → result world))
    (fromRight : Entails Γ (fun world => right world → result world)) :
    Entails Γ result := by
  intro world compatible
  exact (choice world compatible).elim
    (fromLeft world compatible) (fromRight world compatible)

/-!
## The certified-knowledge API

`CertifiedKnowledge` is the semantic image of the runtime smart-constructor API: an empty value is
sound, a fact enters only with a certificate, and projection and truncation preserve soundness.
The runtime `Afaik` has a private constructor precisely so that these are the only ways
to build one.
-/

/-- A knowledge value bundled with its semantic certificate. -/
structure CertifiedKnowledge {World : Type u} {Root : Type v}
    (Γ : Context World) (root : World → Root) where
  value : Knowledge World Root
  root_eq : value.root = root
  certificate : value.Sound Γ

/-- Empty knowledge is sound. -/
def CertifiedKnowledge.empty {World : Type u} {Root : Type v}
    (Γ : Context World) (root : World → Root) :
    CertifiedKnowledge Γ root where
  value := { root, facts := [] }
  root_eq := rfl
  certificate := by
    intro fact present
    contradiction

/-- Add one fact only when its entailment certificate is available. -/
def CertifiedKnowledge.add {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root) (fact : Fact World)
    (proof : Entails Γ fact) : CertifiedKnowledge Γ root where
  value := { knowledge.value with facts := fact :: knowledge.value.facts }
  root_eq := knowledge.root_eq
  certificate := by
    intro fact present
    simp only [List.mem_cons] at present
    rcases present with rfl | present
    · exact proof
    · exact knowledge.certificate present

/-- Select any subset of known facts while preserving the same root. -/
def CertifiedKnowledge.project {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root)
    (facts : List (Fact World))
    (subset : ∀ {fact}, fact ∈ facts → fact ∈ knowledge.value.facts) :
    CertifiedKnowledge Γ root where
  value := { knowledge.value with facts }
  root_eq := knowledge.root_eq
  certificate := fun present => knowledge.certificate (subset present)

/-- Change the operational truncation flag without changing semantic content. -/
def CertifiedKnowledge.withTruncated {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root)
    (truncated : Bool) : CertifiedKnowledge Γ root where
  value := { knowledge.value with truncated }
  root_eq := knowledge.root_eq
  certificate := knowledge.certificate

/-- Fact admission is sound whenever the supplied entailment certificate is valid. -/
theorem fact_admission_sound {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root)
    (fact : Fact World) (certificate : Entails Γ fact) :
    (knowledge.add fact certificate).value.Sound Γ :=
  (knowledge.add fact certificate).certificate

/-- Root projection, modeled as fact deletion, preserves soundness. -/
theorem projection_preserves_soundness {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root)
    (facts : List (Fact World))
    (subset : ∀ {fact : Fact World}, fact ∈ facts → fact ∈ knowledge.value.facts) :
    (knowledge.project facts subset).value.Sound Γ :=
  (knowledge.project facts subset).certificate

/-- Bounded search may set `truncated`, but its certified prefix remains sound. -/
theorem truncation_preserves_soundness {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root)
    (truncated : Bool) :
    (knowledge.withTruncated truncated).value.Sound Γ :=
  (knowledge.withTruncated truncated).certificate

/-- Adding assumptions narrows possible worlds and preserves existing entailments. -/
theorem Entails.strengthen {Γ Γ' : Context World} {fact : Fact World}
    (stronger : ∀ world, Γ' world → Γ world) (proof : Entails Γ fact) :
    Entails Γ' fact := by
  intro world compatible
  exact proof world (stronger world compatible)

/-- Adding assumptions preserves the soundness of an existing knowledge value. -/
theorem Knowledge.Sound.strengthen {Γ Γ' : Context World}
    {knowledge : Knowledge World Root} (sound : knowledge.Sound Γ)
    (stronger : ∀ world, Γ' world → Γ world) : knowledge.Sound Γ' := by
  intro fact present
  exact (sound present).strengthen stronger

/-!
## Inconsistency
-/

/-- A context is consistent when it admits at least one possible world. -/
def Consistent (Γ : Context World) : Prop :=
  ∃ world, Γ world

/-- A context is inconsistent when it entails `False`. -/
def Inconsistent (Γ : Context World) : Prop :=
  Entails Γ (fun _ => False)

/-- Entailing `False` is exactly the absence of a compatible world. -/
theorem inconsistent_iff_not_consistent (Γ : Context World) :
    Inconsistent Γ ↔ ¬ Consistent Γ := by
  constructor
  · intro inconsistent ⟨world, compatible⟩
    exact inconsistent world compatible
  · intro notConsistent world compatible
    exact notConsistent ⟨world, compatible⟩

/-- An inconsistent context entails every fact, explaining the separate result constructor. -/
theorem inconsistent_entails {World : Type u} {Γ : Context World}
    (inconsistent : Inconsistent Γ) (fact : Fact World) :
    Entails Γ fact := by
  intro world compatible
  exact False.elim (inconsistent world compatible)

/-- The semantic result type makes ordinary knowledge and inconsistency disjoint cases. -/
inductive CertifiedResult {World : Type u} {Root : Type v}
    (Γ : Context World) (root : World → Root) where
  | knowledge (value : CertifiedKnowledge Γ root)
  | inconsistent (certificate : Inconsistent Γ)

/-!
## The snapshot contract

The results so far are stated one fact, one conjunction, or one existential at a time. A consumer
receives a whole finished result, so this section restates them for that unit. A `Snapshot` is the
semantic image of a finished runtime result: the selected root, the finite checked facts, the
witness groups identifying which facts came from one existential proof, and the status of the
finite run. The context in which its terms are meaningful is the type index `Γ`, so a snapshot
cannot be separated from its context.

`ValidSnapshot Γ root maxFacts K` is a validity judgment: it says which snapshots are acceptable
answers about `root` in `Γ` under the fact bound, and its rules are the runtime smart constructors
one for one. It is not an operational semantics of `wdyk`. The `certify` rule admits any entailed
fact, `withTruncated` records either status, and the only policy content it constrains is the fact
bound, so it does not say which facts a run finds, which rules were enabled, or whether saturation
really occurred. Instantiating the judgment for an actual run would need trace evidence per fact,
which is the subject of issue #3. What it does give a consumer are the laws:

1. every fact in `K` follows from `Γ` (`ValidSnapshot.sound`, `ValidSnapshot.entails`), and so
   does the combined proposition `⟦K⟧` (`ValidSnapshot.interp`), which is `False` for an
   inconsistent snapshot;
2. facts projected from one existential proof refer to one shared witness
   (`ValidSnapshot.shared`, `ValidSnapshot.shared_witness`, `ValidSnapshot.witness_facts`);
3. relevance projection and truncation preserve soundness (`Snapshot.Sound.project`,
   `Snapshot.Sound.withTruncated`, and the `project` and `withTruncated` rules); and
4. the status says whether the finite run saturated or stopped early. An inconsistent status is
   certified (`ValidSnapshot.inconsistent_certified`); a saturated one is not a completeness claim
   (`saturated_not_complete`).

Nothing here says how a consumer renders a snapshot. There are no atoms, tuples, or labels: only
worlds, facts, and witnesses.
-/

/-- The outcome of one finite extraction run. -/
inductive Status where
  /-- The configured finite run reached a fixpoint. This is not logical completeness. -/
  | saturated
  /-- A configured bound stopped the run before a fixpoint. -/
  | truncated
  /-- The context was found contradictory, so no ordinary knowledge is reported. -/
  | inconsistent
  deriving DecidableEq, Repr

/-- Whether a status reports an early stop. -/
@[expose] def Status.isTruncated : Status → Bool
  | .truncated => true
  | _ => false

/--
One existential proof's shared unknown, together with the predicates the snapshot states about it.
The witness is a function of the compatible world, exactly as in `exists_shared_witness`; a
predicate `p` in the group stands for the fact `group.fact p` about that witness.
-/
structure WitnessGroup {World : Type u} (Γ : Context World) where
  /-- The type of the unknown. -/
  Value : Type u
  /-- The one witness every predicate in the group refers to. -/
  witness : ∀ world, Γ world → Value
  /-- The predicates stated about the witness. -/
  predicates : List (World → Value → Prop)

/-- The fact a group states about one of its predicates: the shared witness satisfies it. -/
@[expose] def WitnessGroup.fact {Γ : Context World} (group : WitnessGroup Γ)
    (predicate : World → group.Value → Prop) : Fact World :=
  fun world => ∃ compatible : Γ world, predicate world (group.witness world compatible)

/-- All facts a group contributes to a snapshot. -/
@[expose] def WitnessGroup.facts {Γ : Context World} (group : WitnessGroup Γ) :
    List (Fact World) :=
  group.predicates.map group.fact

/-- A group is sound when its one witness satisfies every predicate in every compatible world. -/
@[expose] def WitnessGroup.Sound {Γ : Context World} (group : WitnessGroup Γ) : Prop :=
  ∀ predicate ∈ group.predicates, WitnessSatisfies Γ group.witness predicate

/-- Each fact stated by a sound group is entailed. -/
theorem WitnessGroup.Sound.entails_fact {Γ : Context World} {group : WitnessGroup Γ}
    (sound : group.Sound) {predicate : World → group.Value → Prop}
    (mem : predicate ∈ group.predicates) : Entails Γ (group.fact predicate) :=
  fun world compatible => ⟨compatible, sound predicate mem world compatible⟩

/--
The consumer-facing reading of witness identity: in every compatible world one value satisfies all
of the group's predicates at once. `unshared_witnesses_lossy` shows this fails for separately
witnessed predicates.
-/
theorem WitnessGroup.Sound.shared {Γ : Context World} {group : WitnessGroup Γ}
    (sound : group.Sound) :
    Entails Γ (fun world => ∃ value : group.Value,
      ∀ predicate ∈ group.predicates, predicate world value) :=
  fun world compatible =>
    ⟨group.witness world compatible, fun predicate mem => sound predicate mem world compatible⟩

/-- Keep the predicates whose facts survive a selection; the witness is unchanged. -/
@[expose] def WitnessGroup.restrict {Γ : Context World} (group : WitnessGroup Γ)
    (keep : Fact World → Bool) : WitnessGroup Γ :=
  { group with predicates := group.predicates.filter fun predicate => keep (group.fact predicate) }

/-- Restriction preserves soundness. -/
theorem WitnessGroup.Sound.restrict {Γ : Context World} {group : WitnessGroup Γ}
    (sound : group.Sound) (keep : Fact World → Bool) : (group.restrict keep).Sound :=
  fun predicate mem => sound predicate (List.mem_filter.mp mem).1

/--
Open an existential whose body is the conjunction of `predicates` with one chosen witness. This is
the group-level form of `exists_shared_witness`, and the semantic counterpart of the one
`Classical.choose` term the runtime creates per existential.
-/
@[expose] noncomputable def WitnessGroup.open {Γ : Context World} {α : Type u}
    (predicates : List (World → α → Prop))
    (proof : Entails Γ (fun world => ∃ value : α, ∀ predicate ∈ predicates, predicate world value)) :
    WitnessGroup Γ where
  Value := α
  witness := fun world compatible => Classical.choose (proof world compatible)
  predicates := predicates

/-- An opened existential is a sound group. -/
theorem WitnessGroup.open_sound {Γ : Context World} {α : Type u}
    {predicates : List (World → α → Prop)}
    (proof : Entails Γ (fun world => ∃ value : α, ∀ predicate ∈ predicates, predicate world value)) :
    (WitnessGroup.open predicates proof).Sound :=
  fun predicate mem world compatible => Classical.choose_spec (proof world compatible) predicate mem

/--
Existential decomposition into one group is lossless. This generalizes `exists_shared_witness_iff`
from two components to any finite list of predicates.
-/
theorem exists_shared_group_iff {Γ : Context World} {α : Type u}
    {predicates : List (World → α → Prop)} :
    Entails Γ (fun world => ∃ value : α, ∀ predicate ∈ predicates, predicate world value) ↔
      ∃ witness : ∀ world, Γ world → α,
        ∀ predicate ∈ predicates, WitnessSatisfies Γ witness predicate := by
  constructor
  · intro proof
    exact ⟨fun world compatible => Classical.choose (proof world compatible),
      fun predicate mem world compatible =>
        Classical.choose_spec (proof world compatible) predicate mem⟩
  · intro ⟨witness, satisfies⟩ world compatible
    exact ⟨witness world compatible, fun predicate mem => satisfies predicate mem world compatible⟩

/--
A witness-aware snapshot of finite checked knowledge about a selected root. The context `Γ` in
which the facts and witnesses are meaningful is the type index. The runtime counterpart is
`Iykyk.Snapshot`, produced from a finished `WdykResult` by `WdykResult.snapshot`.
-/
structure Snapshot {World : Type u} (Γ : Context World) (Root : Type v) where
  /-- The selected root. -/
  root : World → Root
  /-- The finite checked facts. -/
  facts : List (Fact World)
  /-- Which facts came from one existential proof and share its witness. -/
  witnesses : List (WitnessGroup Γ)
  /-- The outcome of the finite run. -/
  status : Status

/--
A snapshot is sound when every fact follows from the context, every witness group is sound, and an
inconsistent status is backed by a proof that the context entails `False`.
-/
@[expose] def Snapshot.Sound {Γ : Context World} (K : Snapshot Γ Root) : Prop :=
  (∀ fact ∈ K.facts, Entails Γ fact) ∧ (∀ group ∈ K.witnesses, group.Sound) ∧
    (K.status = .inconsistent → Inconsistent Γ)

/-- Witness groups point into the fact list: every fact a group states is a fact of the snapshot. -/
@[expose] def Snapshot.Coherent {Γ : Context World} (K : Snapshot Γ Root) : Prop :=
  ∀ group ∈ K.witnesses, ∀ predicate ∈ group.predicates, group.fact predicate ∈ K.facts

/--
The single proposition a snapshot expresses, the design document's `⟦K⟧`. An inconsistent
snapshot expresses `False`, whatever else it carries; any other snapshot expresses that every fact
holds and each witness group is satisfied by one value. The runtime counterpart is the
certificate of `Iykyk.Snapshot`: `Afaik.certificate` for ordinary knowledge and the proof of
`False` for an `Inconsistency`.
-/
@[expose] def Snapshot.interp {Γ : Context World} (K : Snapshot Γ Root) : Fact World :=
  fun world =>
    match K.status with
    | .inconsistent => False
    | _ => (∀ fact ∈ K.facts, fact world) ∧
        ∀ group ∈ K.witnesses, ∃ value : group.Value,
          ∀ predicate ∈ group.predicates, predicate world value

/-- Forget witness groups and status, keeping the truncation bit. -/
@[expose] def Snapshot.toKnowledge {Γ : Context World} (K : Snapshot Γ Root) :
    Knowledge World Root :=
  { root := K.root, facts := K.facts, truncated := K.status.isTruncated }

/-- A sound snapshot entails its combined proposition, in both the ordinary and the inconsistent case. -/
theorem Snapshot.Sound.interp {Γ : Context World} {K : Snapshot Γ Root} (sound : K.Sound) :
    Entails Γ K.interp := by
  intro world compatible
  unfold Snapshot.interp
  split
  next inconsistent => exact sound.2.2 inconsistent world compatible
  next =>
    exact ⟨fun fact mem => sound.1 fact mem world compatible,
      fun group mem => (sound.2.1 group mem).shared world compatible⟩

/-- A sound snapshot forgets to sound knowledge in the earlier API. -/
theorem Snapshot.Sound.toKnowledge {Γ : Context World} {K : Snapshot Γ Root} (sound : K.Sound) :
    K.toKnowledge.Sound Γ :=
  fun mem => sound.1 _ mem

/-!
### Snapshot operations

These are the semantic images of the runtime smart constructors. `Afaik` has a private
constructor, so a runtime result can only arise through them, and each preserves soundness and
coherence.
-/

/-- Empty knowledge about a root. Runtime: `Afaik.empty`. -/
@[expose] def Snapshot.empty (Γ : Context World) (root : World → Root) : Snapshot Γ Root :=
  { root, facts := [], witnesses := [], status := .saturated }

/-- The result for a contradictory context: no ordinary knowledge. Runtime: `Inconsistency`. -/
@[expose] def Snapshot.inconsistent (Γ : Context World) (root : World → Root) : Snapshot Γ Root :=
  { root, facts := [], witnesses := [], status := .inconsistent }

/-- Record one fact. Runtime: `Afaik.addFact`. -/
@[expose] def Snapshot.add {Γ : Context World} (K : Snapshot Γ Root) (fact : Fact World) :
    Snapshot Γ Root :=
  { K with facts := fact :: K.facts }

/--
Open one existential: its group and the facts it states enter together. Runtime:
`Afaik.addWitness` followed by `addFact` for each decomposed component.
-/
@[expose] def Snapshot.openExists {Γ : Context World} (K : Snapshot Γ Root)
    (group : WitnessGroup Γ) : Snapshot Γ Root :=
  { K with facts := group.facts ++ K.facts, witnesses := group :: K.witnesses }

/--
Keep a selection of facts and groups; a kept group keeps only the predicates whose facts survive.
Runtime: `Afaik.project`, of which relevance projection to the root's connected component
(`projectToRoot`) is one instance.
-/
@[expose] def Snapshot.project {Γ : Context World} (K : Snapshot Γ Root)
    (keepFact : Fact World → Bool) (keepGroup : WitnessGroup Γ → Bool) : Snapshot Γ Root :=
  { K with
    facts := K.facts.filter keepFact
    witnesses := (K.witnesses.filter keepGroup).map (·.restrict keepFact) }

/-- Record whether bounded search stopped early. Runtime: `Afaik.withTruncated`. -/
@[expose] def Snapshot.withTruncated {Γ : Context World} (K : Snapshot Γ Root)
    (truncated : Bool) : Snapshot Γ Root :=
  { K with status := if truncated then .truncated else .saturated }

theorem Snapshot.Sound.empty {Γ : Context World} (root : World → Root) :
    (Snapshot.empty Γ root).Sound :=
  ⟨fun _ mem => (nomatch mem), fun _ mem => (nomatch mem), fun eq => nomatch eq⟩

/-- The inconsistent snapshot is sound exactly when the contradiction is certified. -/
theorem Snapshot.Sound.inconsistent {Γ : Context World} (root : World → Root)
    (certificate : Inconsistent Γ) : (Snapshot.inconsistent Γ root).Sound :=
  ⟨fun _ mem => (nomatch mem), fun _ mem => (nomatch mem), fun _ => certificate⟩

/-- Adding a certified fact preserves soundness. -/
theorem Snapshot.Sound.add {Γ : Context World} {K : Snapshot Γ Root} (sound : K.Sound)
    {fact : Fact World} (proof : Entails Γ fact) : (K.add fact).Sound := by
  refine ⟨fun fact' mem => ?_, sound.2.1, sound.2.2⟩
  rcases List.mem_cons.mp mem with rfl | mem
  · exact proof
  · exact sound.1 _ mem

/-- Opening a sound group preserves soundness. -/
theorem Snapshot.Sound.openExists {Γ : Context World} {K : Snapshot Γ Root} (sound : K.Sound)
    {group : WitnessGroup Γ} (groupSound : group.Sound) : (K.openExists group).Sound := by
  refine ⟨fun fact mem => ?_, fun group' mem => ?_, sound.2.2⟩
  · rcases List.mem_append.mp mem with mem | mem
    · obtain ⟨predicate, memPredicate, rfl⟩ := List.mem_map.mp mem
      exact groupSound.entails_fact memPredicate
    · exact sound.1 _ mem
  · rcases List.mem_cons.mp mem with rfl | mem
    · exact groupSound
    · exact sound.2.1 _ mem

/-- Relevance projection preserves soundness. -/
theorem Snapshot.Sound.project {Γ : Context World} {K : Snapshot Γ Root} (sound : K.Sound)
    (keepFact : Fact World → Bool) (keepGroup : WitnessGroup Γ → Bool) :
    (K.project keepFact keepGroup).Sound := by
  refine ⟨fun fact mem => ?_, fun group mem => ?_, sound.2.2⟩
  · exact sound.1 _ (List.mem_filter.mp mem).1
  · obtain ⟨group', mem', rfl⟩ := List.mem_map.mp mem
    exact (sound.2.1 _ (List.mem_filter.mp mem').1).restrict keepFact

/-- Truncation preserves soundness: the status changes no semantic content. -/
theorem Snapshot.Sound.withTruncated {Γ : Context World} {K : Snapshot Γ Root} (sound : K.Sound)
    (truncated : Bool) : (K.withTruncated truncated).Sound :=
  ⟨sound.1, sound.2.1, fun eq => by cases truncated <;> exact nomatch eq⟩

theorem Snapshot.Coherent.empty {Γ : Context World} (root : World → Root) :
    (Snapshot.empty Γ root).Coherent :=
  fun _ mem => nomatch mem

theorem Snapshot.Coherent.inconsistent {Γ : Context World} (root : World → Root) :
    (Snapshot.inconsistent Γ root).Coherent :=
  fun _ mem => nomatch mem

theorem Snapshot.Coherent.add {Γ : Context World} {K : Snapshot Γ Root} (coherent : K.Coherent)
    (fact : Fact World) : (K.add fact).Coherent :=
  fun group mem predicate memPredicate =>
    List.mem_cons_of_mem _ (coherent group mem predicate memPredicate)

theorem Snapshot.Coherent.openExists {Γ : Context World} {K : Snapshot Γ Root}
    (coherent : K.Coherent) (group : WitnessGroup Γ) : (K.openExists group).Coherent := by
  intro group' mem predicate memPredicate
  rcases List.mem_cons.mp mem with rfl | mem
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨predicate, memPredicate, rfl⟩)
  · exact List.mem_append_right _ (coherent _ mem _ memPredicate)

theorem Snapshot.Coherent.project {Γ : Context World} {K : Snapshot Γ Root}
    (coherent : K.Coherent) (keepFact : Fact World → Bool) (keepGroup : WitnessGroup Γ → Bool) :
    (K.project keepFact keepGroup).Coherent := by
  intro group' mem predicate memPredicate
  obtain ⟨group, memGroup, rfl⟩ := List.mem_map.mp mem
  obtain ⟨memPredicate, kept⟩ := List.mem_filter.mp memPredicate
  exact List.mem_filter.mpr
    ⟨coherent _ (List.mem_filter.mp memGroup).1 _ memPredicate, kept⟩

theorem Snapshot.Coherent.withTruncated {Γ : Context World} {K : Snapshot Γ Root}
    (coherent : K.Coherent) (truncated : Bool) : (K.withTruncated truncated).Coherent :=
  coherent

/-!
### The validity judgment
-/

/--
`ValidSnapshot Γ root maxFacts K` says that `K` is an acceptable snapshot about `root` in context
`Γ` with at most `maxFacts` facts. Each rule is one runtime smart constructor. Facts enter through
three doors only: a derivation in the calculus (`derive`), an externally certified fact whose
runtime counterpart is a kernel-checked proof term (`certify`), and existential opening with one
shared witness (`openExists`). There is no rule that admits an uncertified fact and no rule that
chooses a disjunctive branch.

This is a validity judgment, not an extraction semantics. It is satisfied by every snapshot a
correct run may return, but also by snapshots no run returns: `certify` accepts any entailed fact
and `withTruncated` either status. The fact bound is the only piece of `Config` it constrains.
-/
inductive ValidSnapshot {World : Type u} {Root : Type v} (Γ : Context World) (root : World → Root)
    (maxFacts : Nat) : Snapshot Γ Root → Prop where
  /-- Extraction starts from empty knowledge about the root. -/
  | empty : ValidSnapshot Γ root maxFacts (Snapshot.empty Γ root)
  /-- A fact derived in the calculus from hypotheses the context entails. -/
  | derive {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K)
      {hyps : List (Fact World)} (hypsHold : ∀ fact ∈ hyps, Entails Γ fact)
      {fact : Fact World} (derivation : Derivation.{u, u + 1} hyps fact)
      (bound : K.facts.length < maxFacts) :
      ValidSnapshot Γ root maxFacts (K.add fact)
  /-- An externally certified fact; at runtime, a proof term checked by the kernel. -/
  | certify {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K)
      {fact : Fact World} (certificate : Entails Γ fact)
      (bound : K.facts.length < maxFacts) :
      ValidSnapshot Γ root maxFacts (K.add fact)
  /-- An existential opened with one shared witness. -/
  | openExists {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K)
      (group : WitnessGroup Γ) (sound : group.Sound)
      (bound : K.facts.length + group.predicates.length ≤ maxFacts) :
      ValidSnapshot Γ root maxFacts (K.openExists group)
  /-- Relevance projection: any selection of facts and groups. -/
  | project {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K)
      (keepFact : Fact World → Bool) (keepGroup : WitnessGroup Γ → Bool) :
      ValidSnapshot Γ root maxFacts (K.project keepFact keepGroup)
  /-- Bounded search records whether it stopped early. -/
  | withTruncated {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K)
      (truncated : Bool) :
      ValidSnapshot Γ root maxFacts (K.withTruncated truncated)
  /-- A checked contradiction returns the inconsistent snapshot instead of arbitrary facts. -/
  | inconsistent (certificate : Inconsistent Γ) :
      ValidSnapshot Γ root maxFacts (Snapshot.inconsistent Γ root)

/-- A valid snapshot is about the selected root. -/
theorem ValidSnapshot.root_eq {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} : ValidSnapshot Γ root maxFacts K → K.root = root
  | .empty => rfl
  | .derive valid .. => valid.root_eq
  | .certify valid .. => valid.root_eq
  | .openExists valid .. => valid.root_eq
  | .project valid .. => valid.root_eq
  | .withTruncated valid _ => valid.root_eq
  | .inconsistent _ => rfl

/--
Laws 1, 2, and 4 together: every fact of a valid snapshot follows from the context, every witness
group is sound, and an inconsistent status is certified. Each rule must be checked here, so a rule
admitting an un-entailed fact, an unshared witness, or an unproved contradiction would make this
theorem unprovable.
-/
theorem ValidSnapshot.sound {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} : ValidSnapshot Γ root maxFacts K → K.Sound
  | .empty => .empty root
  | .derive valid hypsHold derivation _ => valid.sound.add (derivation.sound_of hypsHold)
  | .certify valid certificate _ => valid.sound.add certificate
  | .openExists valid _ groupSound _ => valid.sound.openExists groupSound
  | .project valid keepFact keepGroup => valid.sound.project keepFact keepGroup
  | .withTruncated valid truncated => valid.sound.withTruncated truncated
  | .inconsistent certificate => .inconsistent root certificate

/-- Law 1: every fact in a valid snapshot is entailed by the context. -/
theorem ValidSnapshot.entails {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K) {fact : Fact World}
    (mem : fact ∈ K.facts) : Entails Γ fact :=
  valid.sound.1 fact mem

/-- The whole snapshot: the context entails the combined proposition `⟦K⟧`. -/
theorem ValidSnapshot.interp {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K) : Entails Γ K.interp :=
  valid.sound.interp

/-- Law 2: every witness group of a valid snapshot is sound. -/
theorem ValidSnapshot.shared {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K) {group : WitnessGroup Γ}
    (mem : group ∈ K.witnesses) : group.Sound :=
  valid.sound.2.1 group mem

/--
Law 2, consumer form: for each witness group, one value satisfies all of its predicates in every
compatible world. This is what connects existential decomposition to the witness identities the
snapshot retains.
-/
theorem ValidSnapshot.shared_witness {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K) {group : WitnessGroup Γ}
    (mem : group ∈ K.witnesses) :
    Entails Γ (fun world => ∃ value : group.Value,
      ∀ predicate ∈ group.predicates, predicate world value) :=
  (valid.shared mem).shared

/-- Witness groups of a valid snapshot identify facts that are in the snapshot. -/
theorem ValidSnapshot.witness_facts {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} : ValidSnapshot Γ root maxFacts K → K.Coherent
  | .empty => .empty root
  | .derive valid .. => valid.witness_facts.add _
  | .certify valid .. => valid.witness_facts.add _
  | .openExists valid group .. => valid.witness_facts.openExists group
  | .project valid keepFact keepGroup => valid.witness_facts.project keepFact keepGroup
  | .withTruncated valid truncated => valid.witness_facts.withTruncated truncated
  | .inconsistent _ => .inconsistent root

/-- The snapshot is finite: it respects the fact bound. -/
theorem ValidSnapshot.bounded {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} : ValidSnapshot Γ root maxFacts K → K.facts.length ≤ maxFacts
  | .empty => Nat.zero_le _
  | .derive _ _ _ bound => bound
  | .certify _ _ bound => bound
  | .openExists (K := K) _ group _ bound => by
      show (group.facts ++ K.facts).length ≤ maxFacts
      rw [List.length_append, WitnessGroup.facts, List.length_map, Nat.add_comm]
      exact bound
  | .project valid _ _ => Nat.le_trans (List.length_filter_le _ _) valid.bounded
  | .withTruncated valid _ => valid.bounded
  | .inconsistent _ => Nat.zero_le _

/-- Law 4: an inconsistent status is certified. -/
theorem ValidSnapshot.inconsistent_certified {Γ : Context World} {root : World → Root}
    {maxFacts : Nat} {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K)
    (inconsistent : K.status = .inconsistent) : Inconsistent Γ :=
  valid.sound.2.2 inconsistent

/-- A valid snapshot is certified knowledge in the earlier API. -/
def ValidSnapshot.toCertified {Γ : Context World} {root : World → Root} {maxFacts : Nat}
    {K : Snapshot Γ Root} (valid : ValidSnapshot Γ root maxFacts K) :
    CertifiedKnowledge Γ root where
  value := K.toKnowledge
  root_eq := valid.root_eq
  certificate := valid.sound.toKnowledge

/--
Law 4, the negative half: `saturated` is not completeness. The judgment admits a saturated snapshot
that omits an entailed fact, so no consumer may read the status as "every entailed fact is
present".
-/
theorem saturated_not_complete :
    ∃ (World : Type) (Γ : Context World) (root : World → Unit) (maxFacts : Nat)
      (K : Snapshot Γ Unit) (fact : Fact World),
      ValidSnapshot Γ root maxFacts K ∧ K.status = .saturated ∧ Entails Γ fact ∧ fact ∉ K.facts :=
  ⟨Unit, fun _ => True, fun _ => (), 0, Snapshot.empty _ _, fun _ => True,
    .empty, rfl, fun _ _ => trivial, nofun⟩

/-!
### Worked instances

The runtime tests in `Iykyk/Examples/Snapshot.lean` have semantic counterparts here: a shared
existential witness, a run that stopped at its fact bound, and an inconsistent context.
-/

namespace Instances

/-- A world is an edge relation on `Nat`. The context says a two-step route from `0` to `1` exists. -/
def route : Context (Nat → Nat → Prop) :=
  fun edge => ∃ middle, edge 0 middle ∧ edge middle 1

/-- The route's shared middle vertex, with the two edge facts stated about it. -/
noncomputable def middle : WitnessGroup route :=
  WitnessGroup.open [fun edge middle => edge 0 middle, fun edge middle => edge middle 1]
    fun _ ⟨middle, left, right⟩ => ⟨middle, by simp [left, right]⟩

/-- The snapshot `wdyk 0` returns for the route: one group, its two facts, saturated. -/
noncomputable def routeSnapshot : Snapshot route Nat :=
  (Snapshot.empty route fun _ => 0).openExists middle

theorem route_valid : ValidSnapshot route (fun _ => 0) 2 routeSnapshot :=
  .openExists .empty middle (WitnessGroup.open_sound _) (Nat.le_refl _)

/-- Both facts are stated about the one witness of the one group. -/
example : routeSnapshot.facts =
    [middle.fact fun edge m => edge 0 m, middle.fact fun edge m => edge m 1] :=
  rfl

example : routeSnapshot.status = .saturated := rfl

/-- The judgment recovers the route from the group: one value serves both facts. -/
example : Entails route fun edge => ∃ m, edge 0 m ∧ edge m 1 := by
  intro edge compatible
  obtain ⟨m, holds⟩ :=
    route_valid.shared_witness (List.mem_singleton.mpr rfl) edge compatible
  exact ⟨m, holds (fun edge m => edge 0 m) (List.mem_cons_self ..),
    holds (fun edge m => edge m 1) (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

/--
Losslessness at the snapshot level: at any world, the two witness facts jointly rebuild the route,
because they name one witness. Two unrelated witnesses could not (`unshared_witnesses_lossy`).
-/
example (edge : Nat → Nat → Prop) (holds : ∀ fact ∈ routeSnapshot.facts, fact edge) :
    ∃ m, edge 0 m ∧ edge m 1 := by
  obtain ⟨compatible, left⟩ := holds _ (List.mem_cons_self ..)
  obtain ⟨_, right⟩ := holds _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact ⟨middle.witness edge compatible, left, right⟩

/-- A world is a predicate on `Nat`. The context seeds `0` and steps forward without end. -/
def reach : Context (Nat → Prop) :=
  fun world => world 0 ∧ ∀ n, world n → world (n + 1)

def seed : Fact (Nat → Prop) := fun world => world 0

def step : Fact (Nat → Prop) := fun world => ∀ n, world n → world (n + 1)

theorem reach_hyps : ∀ fact ∈ [seed, step], Entails reach fact := by
  intro fact mem world compatible
  rcases List.mem_cons.mp mem with rfl | mem
  · exact compatible.1
  · rcases List.mem_singleton.mp mem with rfl
    exact compatible.2

/-- Under `maxFacts := 2`, extraction reports the seed and one forward step, then stops. -/
def reachSnapshot : Snapshot reach Nat :=
  (((Snapshot.empty reach fun _ => 0).add seed).add fun world => world (0 + 1)).withTruncated true

/-- Both facts are derived in the calculus; the second is forward application of an instance. -/
theorem reach_valid : ValidSnapshot reach (fun _ => 0) 2 reachSnapshot :=
  .withTruncated
    (.derive (.derive .empty reach_hyps (.hyp (List.mem_cons_self ..)) (by decide))
      reach_hyps
      (.forward (.hyp (List.mem_cons_self ..))
        (.instantiate (predicate := fun (world : Nat → Prop) n => world n → world (n + 1)) 0
          (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
      (by decide))
    true

example : reachSnapshot.status = .truncated := rfl

example : reachSnapshot.facts.length ≤ 2 := reach_valid.bounded

/-- Truncation is honest: `world 2` is entailed but not reported, and the status says so. -/
example : Entails reach (fun world => world 2) ∧
    (fun world : Nat → Prop => world 2) ∉ reachSnapshot.facts := by
  refine ⟨fun world ⟨zero, next⟩ => next 1 (next 0 zero), fun mem => ?_⟩
  simp only [reachSnapshot, Snapshot.withTruncated, Snapshot.add, Snapshot.empty,
    List.mem_cons] at mem
  rcases mem with eq | eq | eq
  · have := congrFun eq fun n => n = 2
    simp at this
  · have := congrFun eq fun n => n = 2
    simp [seed] at this
  · exact nomatch eq

/-- A context that asserts a predicate and its negation is inconsistent. -/
def clash : Context (Nat → Prop) := fun world => world 0 ∧ ¬ world 0

theorem clash_inconsistent : Inconsistent clash := fun _ ⟨yes, no⟩ => no yes

/-- The inconsistent snapshot expresses `False`, not the empty conjunction. -/
example : ValidSnapshot clash (fun _ => 0) 0 (Snapshot.inconsistent clash fun _ => 0) :=
  .inconsistent clash_inconsistent

example : (Snapshot.inconsistent clash fun _ => (0 : Nat)).interp = fun _ => False := rfl

end Instances

end Iykyk.Metatheory
