module

public import Iykyk
meta import Iykyk

public section

/-!
# Snapshot contract tests

These tests pin the runtime side of the snapshot contract (`Iykyk/Snapshot.lean`) to the laws
proved in `metatheory/IykykMetatheory.lean`:

* a shared existential witness yields one witness group whose facts are exactly the facts that
  mention its term, and a certificate that binds that witness once (`Extracts.shared_witness`,
  `Extracts.witness_facts`);
* a productive rule under a small fact bound reports `truncated` and respects the bound
  (`Extracts.bounded`; the status is not a completeness claim);
* a contradiction reports `inconsistent` with `False` certified and no ordinary facts
  (`Extracts.inconsistent_certified`); and
* relevance projection drops a witness together with the facts that mentioned it, so the kept
  groups still index facts of the snapshot (`Snapshot.Sound.project`, `Extracts.witness_facts`).
-/

namespace Iykyk.Examples.Snapshot

open Lean Meta Elab Tactic

set_option linter.unusedVariables false

private meta def mentions (proposition term : Expr) : Bool :=
  proposition == term || (proposition.find? (· == term)).isSome

private meta def snapshotOf (rootStx : Syntax) (config : Config := {}) : TacticM Snapshot := do
  let root ← instantiateMVars (← Term.elabTerm rootStx none)
  (← wdyk root config).snapshot

private meta def elaborateRules (stxs : Array Syntax) : TacticM (Array Expr) :=
  stxs.mapM fun stx => do instantiateMVars (← Term.elabTerm stx none)

private meta def expectStatus (stx : Syntax) (snapshot : Snapshot) (expected : Status) :
    TacticM Unit := do
  unless snapshot.status == expected do
    throwErrorAt stx "expected status {repr expected}, found {repr snapshot.status}"

/-- Every group indexes facts of the snapshot, and each indexed fact mentions the witness. -/
private meta def expectCoherentGroups (stx : Syntax) (snapshot : Snapshot) : TacticM Unit := do
  for group in snapshot.witnesses do
    for index in group.facts do
      unless index < snapshot.facts.size do
        throwErrorAt stx "witness group {group.witness.id} indexes a missing fact [{index}]"
      unless mentions snapshot.facts[index]!.proposition group.witness.term do
        throwErrorAt stx "fact [{index}] does not mention witness {group.witness.id}"

/-- The certificate is what the kernel accepts in the snapshot's own scope. -/
private meta def expectCertified (snapshot : Snapshot) : TacticM Unit :=
  kernelCheckClaim snapshot.scope snapshot.certificate.proposition snapshot.certificate.proof

private meta def assertSharedWitness (rootStx : Syntax) : TacticM Unit := withMainContext do
  let snapshot ← snapshotOf rootStx
  expectStatus rootStx snapshot .saturated
  unless snapshot.witnesses.size == 1 do
    throwErrorAt rootStx "expected one witness group, found {snapshot.witnesses.size}"
  let group := snapshot.witnesses[0]!
  unless group.facts == #[0, 1] do
    throwErrorAt rootStx "expected the group to identify facts [0, 1], found {repr group.facts}"
  expectCoherentGroups rootStx snapshot
  -- One existential proof, one binder: the certificate binds the shared witness exactly once.
  let certificate := snapshot.certificate.proposition
  unless certificate.isAppOfArity ``Exists 2 do
    throwErrorAt rootStx "expected the certificate to bind the shared witness"
  if certificate.appArg!.bindingBody!.isAppOfArity ``Exists 2 then
    throwErrorAt rootStx "the certificate bound more than one witness"
  expectCertified snapshot

private meta def assertTruncatedWithin (rootStx : Syntax) (ruleStxs : Array Syntax)
    (maxFacts : Nat) : TacticM Unit := withMainContext do
  let snapshot ← snapshotOf rootStx { hypotheses := ← elaborateRules ruleStxs, maxFacts }
  expectStatus rootStx snapshot .truncated
  unless snapshot.facts.size ≤ maxFacts do
    throwErrorAt rootStx "expected at most {maxFacts} facts, found {snapshot.facts.size}"
  expectCertified snapshot

private meta def assertInconsistent (rootStx : Syntax) : TacticM Unit := withMainContext do
  let snapshot ← snapshotOf rootStx
  expectStatus rootStx snapshot .inconsistent
  unless snapshot.facts.isEmpty && snapshot.witnesses.isEmpty do
    throwErrorAt rootStx "an inconsistent snapshot reported ordinary knowledge"
  unless snapshot.certificate.proposition.isConstOf ``False do
    throwErrorAt rootStx "expected the certificate to prove False"
  expectCertified snapshot

private meta def assertWitnessGroups (rootStx : Syntax) (expected : Nat) (rootOnly : Bool) :
    TacticM Unit := withMainContext do
  let snapshot ← snapshotOf rootStx { rootOnly }
  unless snapshot.witnesses.size == expected do
    throwErrorAt rootStx
      "expected {expected} witness groups, found {snapshot.witnesses.size}"
  for group in snapshot.witnesses do
    if group.facts.isEmpty then
      throwErrorAt rootStx "witness group {group.witness.id} identifies no facts"
  expectCoherentGroups rootStx snapshot
  expectCertified snapshot

syntax "guard_iykyk_snapshot_shared " term : tactic
syntax "guard_iykyk_snapshot_truncated_within " num " facts " term " fyi " "[" term,* "]" : tactic
syntax "guard_iykyk_snapshot_inconsistent " term : tactic
syntax "guard_iykyk_snapshot_groups " num " for " term : tactic
syntax "guard_iykyk_snapshot_groups_unprojected " num " for " term : tactic

elab_rules : tactic
  | `(tactic| guard_iykyk_snapshot_shared $root:term) => assertSharedWitness root
  | `(tactic| guard_iykyk_snapshot_truncated_within $bound:num facts $root:term
        fyi [$rules:term,*]) =>
      assertTruncatedWithin root rules.getElems bound.getNat
  | `(tactic| guard_iykyk_snapshot_inconsistent $root:term) => assertInconsistent root
  | `(tactic| guard_iykyk_snapshot_groups $count:num for $root:term) =>
      assertWitnessGroups root count.getNat true
  | `(tactic| guard_iykyk_snapshot_groups_unprojected $count:num for $root:term) =>
      assertWitnessGroups root count.getNat false

variable {Vertex : Type}
variable (edge : Vertex → Vertex → Prop) (Reach P : Vertex → Prop)

-- A shared existential witness: one group, both facts, one binder in the certificate.
example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  guard_iykyk_snapshot_shared source
  trivial

-- A productive rule under a small fact bound: the run stops early and says so.
example (start : Vertex) (next : Vertex → Vertex)
    (seed : Reach start) (step : ∀ x, Reach x → Reach (next x)) : True := by
  guard_iykyk_snapshot_truncated_within 3 facts start fyi [step]
  trivial

-- A contradiction: `False` certified, no ordinary knowledge.
example (start : Vertex) (positive : Reach start) (negative : ¬ Reach start) : True := by
  guard_iykyk_snapshot_inconsistent start
  trivial

-- Two existential proofs give two witnesses. Relevance projection to `source` keeps only the
-- route's witness, and drops the other together with the facts that mentioned it.
example (source target other : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target)
    (elsewhere : ∃ vertex, P vertex ∧ P other) : True := by
  guard_iykyk_snapshot_groups_unprojected 2 for source
  guard_iykyk_snapshot_groups 1 for source
  trivial

end Iykyk.Examples.Snapshot
