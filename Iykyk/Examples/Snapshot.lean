module

public import Iykyk
meta import Iykyk

public section

/-!
# Snapshot contract tests

These tests pin the runtime side of the snapshot contract (`Iykyk/Snapshot.lean`) to the laws
proved in `metatheory/IykykMetatheory.lean`:

* a shared existential witness yields one witness group whose facts are exactly the facts that
  mention its term, and a certificate that binds that witness once
  (`ValidSnapshot.shared_witness`, `ValidSnapshot.witness_facts`);
* a productive rule under a small fact bound reports `truncated` and respects the bound
  (`ValidSnapshot.bounded`; the status is not a completeness claim);
* a contradiction reports `inconsistent` with `False` certified and no ordinary facts
  (`ValidSnapshot.inconsistent_certified`, and `Snapshot.interp` is `False` there);
* relevance projection drops a witness together with the facts that mentioned it, so the kept
  groups still index facts of the snapshot (`Snapshot.Sound.project`,
  `ValidSnapshot.witness_facts`);
* the snapshot boundary kernel-checks the certificate even when `wdyk` was told not to; and
* `Snapshot`, `Afaik`, and `Inconsistency` cannot be forged from outside their module: no
  `Inhabited` instance, no accessible constructor, and no structure update.
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
      let some fact := snapshot.facts[index]?
        | throwErrorAt stx "witness group {group.witness.id} indexes a missing fact [{index}]"
      unless mentions fact.proposition group.witness.term do
        throwErrorAt stx "fact [{index}] does not mention witness {group.witness.id}"

/-- The certificate is what the kernel accepts in the snapshot's own scope. -/
private meta def expectCertified (snapshot : Snapshot) : TacticM Unit :=
  kernelCheckClaim snapshot.scope snapshot.certificate.proposition snapshot.certificate.proof

private meta def assertSharedWitness (rootStx : Syntax) : TacticM Unit := withMainContext do
  let snapshot ← snapshotOf rootStx
  expectStatus rootStx snapshot .saturated
  let #[group] := snapshot.witnesses
    | throwErrorAt rootStx "expected one witness group, found {snapshot.witnesses.size}"
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

/--
With `kernelCheck := false`, `wdyk` skips its own kernel check. The snapshot boundary still runs
one, so the certificate a consumer receives is kernel-checked regardless of that configuration.
-/
private meta def assertCheckedAtBoundary (rootStx : Syntax) : TacticM Unit := withMainContext do
  let snapshot ← snapshotOf rootStx { kernelCheck := false }
  expectStatus rootStx snapshot .saturated
  expectCoherentGroups rootStx snapshot
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
syntax "guard_iykyk_snapshot_truncated_within " num " on " term " fyi " "[" term,* "]" : tactic
syntax "guard_iykyk_snapshot_checked_at_boundary " term : tactic
syntax "guard_iykyk_snapshot_inconsistent " term : tactic
syntax "guard_iykyk_snapshot_groups " num " for " term : tactic
syntax "guard_iykyk_snapshot_groups_unprojected " num " for " term : tactic

elab_rules : tactic
  | `(tactic| guard_iykyk_snapshot_shared $root:term) => assertSharedWitness root
  | `(tactic| guard_iykyk_snapshot_truncated_within $bound:num on $root:term
        fyi [$rules:term,*]) =>
      assertTruncatedWithin root rules.getElems bound.getNat
  | `(tactic| guard_iykyk_snapshot_checked_at_boundary $root:term) =>
      assertCheckedAtBoundary root
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
  guard_iykyk_snapshot_truncated_within 3 on start fyi [step]
  trivial

-- The boundary's own kernel check does not depend on `wdyk`'s configuration.
example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  guard_iykyk_snapshot_checked_at_boundary source
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

/-!
## Trust tests

Holding a `Snapshot`, `Afaik`, or `Inconsistency` is evidence only if there is no way to obtain
one except through the checked path. This file is a different module from the definitions, so
what fails here fails for every consumer.
-/

-- No `Inhabited` instance: `default` would be an unchecked value.
run_meta do
  for typeName in [``Afaik, ``Inconsistency, ``Snapshot] do
    if (← synthInstance? (← mkAppM ``Inhabited #[mkConst typeName])).isSome then
      throwError "{typeName} is Inhabited, so `default` would bypass its checked constructor"

-- The constructor is not accessible by name.
/-- error: Unknown constant `Iykyk.Snapshot.mk` -/
#guard_msgs in
example : Snapshot :=
  Snapshot.mk (mkConst ``True) {} #[] #[] #[] .saturated ⟨mkConst ``True, mkConst ``True.intro⟩

-- Nor through structure instance notation.
/-- error: invalid {...} notation, constructor for `Snapshot` is marked as private -/
#guard_msgs in
example : Snapshot :=
  { root := mkConst ``True, scope := {}, localInstances := #[], facts := #[], witnesses := #[]
    status := .saturated, certificate := ⟨mkConst ``True, mkConst ``True.intro⟩ }

-- Nor can a legitimately obtained snapshot be altered by structure update.
/-- error: invalid {...} notation, constructor for `Snapshot` is marked as private -/
#guard_msgs in
def tamper (snapshot : Snapshot) : Snapshot := { snapshot with status := .saturated }

end Iykyk.Examples.Snapshot
