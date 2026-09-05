module

public import Iykyk.Extract

public section

/-!
# Witness-aware knowledge snapshots

`wdykSnapshot` is the checked boundary for downstream consumers of the first inspection stage
`(Γ, e) → K`. It exposes only finite facts already admitted by `wdyk`, the captured scope and local
instances needed to interpret them, stable groups for existential witnesses, and one kernel-checked
certificate for the whole result.

The snapshot constructor is private and the type has no `Inhabited` instance. In particular, there
is no adapter from an arbitrary `Afaik` or `WdykResult`: every public construction path runs `wdyk`
and then performs the kernel check here, even when `Config.kernelCheck` is false. Relationalization,
atom allocation, tuple construction, and presentation belong to consumers rather than this layer.
-/

namespace Iykyk

open Lean Meta

/-- The exhaustive operational outcome of one snapshot extraction. -/
inductive SnapshotStatus where
  | saturated
  | truncated
  | inconsistent
  deriving Inhabited, BEq, Repr, DecidableEq

/-- One existential witness and the indices of all emitted facts in which its term occurs. -/
structure WitnessGroup where
  witness : Witness
  factIndices : Array Nat
  deriving Inhabited

/--
A finite, kernel-checked view of `wdyk` output. The private constructor and absence of `Inhabited`
make the guarantee a property of every obtainable value, rather than a convention for callers.
-/
structure Snapshot where
  private mk ::
  root : Expr
  scope : LocalContext
  localInstances : LocalInstances
  facts : Array KnownFact
  witnesses : Array WitnessGroup
  status : SnapshotStatus
  /-- `False` for an inconsistent result; otherwise the existential closure of `facts`. -/
  certificate : KnownFact

private def kernelCheckTerm (scope : LocalContext) (term : Expr) : MetaM Unit := do
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then
    throwError "iykyk: kernel checking requires a metavariable-free snapshot term{indentExpr term}"
  match Kernel.check (← getEnv) scope term with
  | .ok _ => return ()
  | .error exception =>
      throwError "iykyk: kernel rejected a snapshot term\n\
        {exception.toMessageData (← getOptions)}"

private def mentionsWitness (fact : KnownFact) (witness : Witness) : MetaM Bool := do
  return (← kabstract fact.proposition witness.term).hasLooseBVars

private def groupWitnesses (knowledge : Afaik) : MetaM (Array WitnessGroup) := do
  let mut groups := #[]
  for witness in knowledge.witnesses do
    let mut factIndices := #[]
    for index in [:knowledge.facts.size] do
      if ← mentionsWitness knowledge.facts[index]! witness then
        factIndices := factIndices.push index
    -- The certificate uses the same `kabstract` occurrence test and omits unused binders.
    unless factIndices.isEmpty do
      groups := groups.push { witness, factIndices }
  return groups

private def snapshotAfaik (knowledge : Afaik) : MetaM Snapshot :=
    withLCtx knowledge.scope knowledge.localInstances do
  kernelCheckTerm knowledge.scope knowledge.root
  let certificate ← knowledge.kernelCertify
  let witnesses ← groupWitnesses knowledge
  for group in witnesses do
    let witness := group.witness
    kernelCheckTerm knowledge.scope witness.type
    kernelCheckTerm knowledge.scope witness.term
  return {
    root := knowledge.root
    scope := knowledge.scope
    localInstances := knowledge.localInstances
    facts := knowledge.facts
    witnesses
    status := if knowledge.truncated then .truncated else .saturated
    certificate
  }

private def snapshotInconsistency (inconsistency : Inconsistency) : MetaM Snapshot :=
    withLCtx inconsistency.scope inconsistency.localInstances do
  kernelCheckTerm inconsistency.scope inconsistency.root
  inconsistency.kernelCertify
  return {
    root := inconsistency.root
    scope := inconsistency.scope
    localInstances := inconsistency.localInstances
    facts := #[]
    witnesses := #[]
    status := .inconsistent
    certificate := { proposition := mkConst ``False, proof := inconsistency.proof }
  }

/--
Compute a finite witness-aware snapshot and kernel-check its root and combined certificate.

Unlike raw `wdyk`, this boundary always performs kernel certification. Its `kernelCheck`
configuration field is therefore used only to avoid a redundant earlier check inside `wdyk`.
-/
def wdykSnapshot (root : Expr) (config : Config := {}) : MetaM Snapshot := do
  match ← wdyk root { config with kernelCheck := false } with
  | .afaik knowledge => snapshotAfaik knowledge
  | .inconsistent inconsistency => snapshotInconsistency inconsistency

end Iykyk
