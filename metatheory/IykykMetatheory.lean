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
def Entails (Γ : Context World) (fact : Fact World) : Prop :=
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
def Knowledge.Sound (Γ : Context World) (knowledge : Knowledge World Root) : Prop :=
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
theorem extract_sound {Γ : Context World} {hyps : List (Fact World)}
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
The runtime `RootedKnowledge` has a private constructor precisely so that these are the only ways
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
    intro candidate present
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

/-- Candidate admission is sound regardless of which engine produced the certificate. -/
theorem candidate_admission_sound {World : Type u} {Root : Type v} {Γ : Context World}
    {root : World → Root} (knowledge : CertifiedKnowledge Γ root)
    (candidate : Fact World) (certificate : Entails Γ candidate) :
    (knowledge.add candidate certificate).value.Sound Γ :=
  (knowledge.add candidate certificate).certificate

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

end Iykyk.Metatheory
