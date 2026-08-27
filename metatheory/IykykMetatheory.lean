module

public import Lean

public section

/-!
# Lightweight metatheory for iykyk

This module gives the semantic core independently of Lean's `Expr` representation. A context is a
set of possible worlds, a fact is a predicate on worlds, and knowledge is sound when every reported
fact holds in every world allowed by the context.

The main theorem, `extract_sound`, says that an extractor is sound whenever every output fact has a
derivation built from checked certificates, conjunction elimination, and forward application.
Projection and truncation cannot invalidate soundness. Existential decomposition preserves one
shared witness, and inconsistency is kept separate because it entails every fact.

Academic lineage: possible-world semantics, proof-carrying code, and refinement-type invariants
motivate this small semantic layer. The metaprogram-to-semantics bridge is documented separately in
`metatheory/README.md`.
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

/-- Semantic knowledge about a distinguished root. -/
structure Knowledge (World : Type u) (Root : Type v) where
  root : World → Root
  facts : List (Fact World)
  truncated : Bool := false

/-- Every fact in a knowledge value follows from its context. -/
def Knowledge.Sound (Γ : Context World) (knowledge : Knowledge World Root) : Prop :=
  ∀ {fact}, fact ∈ knowledge.facts → Entails Γ fact

/-- The proof-producing inference fragment used by the extractor. -/
inductive Derivation {World : Type u} (Γ : Context World) : Fact World → Prop where
  | certificate {fact} (proof : Entails Γ fact) : Derivation Γ fact
  | andLeft {left right : Fact World}
      (proof : Derivation Γ (fun world => left world ∧ right world)) :
      Derivation Γ left
  | andRight {left right : Fact World}
      (proof : Derivation Γ (fun world => left world ∧ right world)) :
      Derivation Γ right
  | forward {premise conclusion : Fact World}
      (premiseProof : Derivation Γ premise)
      (ruleProof : Derivation Γ (fun world => premise world → conclusion world)) :
      Derivation Γ conclusion

/-- Every derivation in the extraction fragment is semantically sound. -/
theorem Derivation.sound {Γ : Context World} {fact : Fact World} :
    Derivation Γ fact → Entails Γ fact
  | .certificate proof => proof
  | .andLeft proof => fun world compatible => (proof.sound world compatible).1
  | .andRight proof => fun world compatible => (proof.sound world compatible).2
  | .forward premiseProof ruleProof => fun world compatible =>
      ruleProof.sound world compatible (premiseProof.sound world compatible)

/-- Abstract extractor soundness: generated derivations certify every output fact. -/
theorem extract_sound {Γ : Context World} {knowledge : Knowledge World Root}
    (generated : ∀ {fact}, fact ∈ knowledge.facts → Derivation Γ fact) :
    knowledge.Sound Γ := by
  intro fact present
  exact (generated present).sound

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

/-- A consequence proved in both branches may be reported without choosing a branch. -/
theorem common_of_disjunction {Γ : Context World} {left right result : Fact World}
    (choice : Entails Γ (fun world => left world ∨ right world))
    (fromLeft : Entails Γ (fun world => left world → result world))
    (fromRight : Entails Γ (fun world => right world → result world)) :
    Entails Γ result := by
  intro world compatible
  exact (choice world compatible).elim
    (fromLeft world compatible) (fromRight world compatible)

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
