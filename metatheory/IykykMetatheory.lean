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

Flattening takes only the input formula. Each existential allocates one typed slot in a
witness assignment. All facts in its body read the same slot. Conjunction uses independent
slots for the witnesses introduced in its two branches. Reading back the output binds one
assignment around the conjunction of all emitted facts.
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

/-- The slots in `Witnesses` name the bound variables shared by the emitted atomic predicates. -/
structure FlatFacts (World : Type u) where
  Witnesses : Type u
  facts : List (Witnesses → World → Prop)

/-- One assignment must satisfy every fact, including when a witness type might be empty. -/
def FlatFacts.readBack {World : Type u} (flat : FlatFacts World) : Fact World :=
  fun world => ∃ assignment : flat.Witnesses, ∀ fact ∈ flat.facts, fact assignment world

/-- Combine two lists of facts and keep their independently introduced witness slots separate. -/
def FlatFacts.combine {World : Type u} (left right : FlatFacts World) : FlatFacts World where
  Witnesses := left.Witnesses × right.Witnesses
  facts := (left.facts.map fun p ws w => p ws.1 w) ++ (right.facts.map fun p ws w => p ws.2 w)

/-- Move the existential variable from the extended world into one shared witness slot. -/
def FlatFacts.bindWitness {α World : Type u} (body : FlatFacts (α × World)) : FlatFacts World where
  Witnesses := α × body.Witnesses
  facts := body.facts.map fun p ws w => p ws.2 (ws.1, w)

theorem FlatFacts.readBack_combine {World : Type u} (left right : FlatFacts World) (w : World) :
    (left.combine right).readBack w ↔ left.readBack w ∧ right.readBack w := by
  constructor
  · rintro ⟨⟨wl, wr⟩, holds⟩
    constructor
    · exact ⟨wl, fun p hp => holds _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))⟩
    · exact ⟨wr, fun p hp => holds _ (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))⟩
  · rintro ⟨⟨wl, hl⟩, ⟨wr, hr⟩⟩
    refine ⟨(wl, wr), ?_⟩
    intro fact mem
    rcases List.mem_append.mp mem with mem | mem
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
      exact hl p hp
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
      exact hr p hp

theorem FlatFacts.readBack_bindWitness {α World : Type u} (body : FlatFacts (α × World)) (w : World) :
    body.bindWitness.readBack w ↔ ∃ value, body.readBack (value, w) := by
  constructor
  · rintro ⟨⟨value, ws⟩, holds⟩
    exact ⟨value, ws, fun p hp => holds _ (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩
  · rintro ⟨value, ws, holds⟩
    refine ⟨(value, ws), ?_⟩
    intro fact mem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
    exact holds p hp

/-- Flatten the structural connectives, leaving one output predicate for each input atom. -/
def Formula.decompose : {World : Type u} → Formula World → FlatFacts World
  | _, .atom p => ⟨PUnit, [fun _ w => p w]⟩
  | _, .conj left right => left.decompose.combine right.decompose
  | _, .ex body => body.decompose.bindWitness

/-- Closing the emitted facts recovers the formula in every world, without assuming it holds. -/
theorem Formula.decompose_lossless : {World : Type u} → (f : Formula World) → (w : World) →
    f.decompose.readBack w ↔ f.interp w
  | _, .atom p, w => by
    constructor
    · rintro ⟨ws, holds⟩
      exact holds _ (List.Mem.head _)
    · intro hp
      refine ⟨PUnit.unit, ?_⟩
      intro fact mem
      obtain rfl := List.mem_singleton.mp mem
      exact hp
  | _, .conj left right, w =>
    (FlatFacts.readBack_combine _ _ w).trans
      (and_congr (left.decompose_lossless w) (right.decompose_lossless w))
  | _, .ex body, w =>
    (FlatFacts.readBack_bindWitness _ w).trans
      (exists_congr fun value => body.decompose_lossless (value, w))

/-- The same witness assignment satisfies all emitted facts in each compatible world. -/
theorem Formula.decompose_sound {World : Type u} (f : Formula World) {Γ : Context World} (h : Entails Γ f.interp) :
    Entails Γ f.decompose.readBack :=
  fun w hw => (f.decompose_lossless w).mpr (h w hw)

/-!
## Counterexamples for the rejected designs

Two simpler designs look plausible and are refuted by concrete contexts. These theorems are the
reason the extractor preserves witness identity and never commits to a disjunctive branch.
-/

/-- Dropping the second atom can make a false existential read back as true. -/
theorem dropping_one_fact_loses_information :
    ∃ f : Formula Unit, ({ f.decompose with facts := f.decompose.facts.take 1 }).readBack () ∧
      ¬ f.interp () := by
  let left : Fact (Bool × Unit) := fun p => p.1 = true
  let right : Fact (Bool × Unit) := fun p => p.1 = false
  refine ⟨.ex (.conj (.atom left) (.atom right)), ?_, ?_⟩
  · refine ⟨(true, PUnit.unit, PUnit.unit), ?_⟩
    intro fact mem
    obtain rfl := List.mem_singleton.mp mem
    rfl
  · rintro ⟨v, hl, hr⟩
    exact Bool.noConfusion (hl.symm.trans hr : true = false)

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

end Iykyk.Metatheory
