module

public import Iykyk
meta import Iykyk

public section

/-!
# Witness-aware snapshot contract tests

These tests exercise the public boundary rather than a parallel model: witness identity and
grouping, status semantics at both bounds, unconditional snapshot certification, captured scope,
inconsistency, and the absence of default construction paths.
-/

namespace Iykyk.Examples.Snapshot

open Lean Meta Elab Tactic

set_option linter.unusedVariables false

private meta def snapshotFor (rootStx : Syntax) (config : Config := {}) : TacticM Snapshot :=
    withMainContext do
  let root ← instantiateMVars (← Term.elabTerm rootStx none)
  wdykSnapshot root config

private meta partial def existentialDepth (proposition : Expr) : Nat :=
  if proposition.isAppOfArity ``Exists 2 then
    match proposition.getAppArgs[1]! with
    | .lam _ _ body _ => 1 + existentialDepth body
    | _ => 0
  else
    0

private meta def guardShared (rootStx : Syntax) : TacticM Unit := do
  let snapshot ← snapshotFor rootStx { kernelCheck := false }
  unless snapshot.status == .saturated do
    throwError "shared-witness extraction did not saturate"
  unless snapshot.facts.size == 2 && snapshot.witnesses.size == 1 do
    throwError "shared-witness extraction returned the wrong fact or witness count"
  let group := snapshot.witnesses[0]!
  unless group.witness.id == 0 && group.factIndices == #[0, 1] do
    throwError "one existential witness was not shared across both facts"
  unless existentialDepth snapshot.certificate.proposition == 1 do
    throwError "one shared witness did not become exactly one certificate binder"
  kernelCheckClaim snapshot.scope snapshot.certificate.proposition snapshot.certificate.proof

private meta def guardDistinct (rootStx : Syntax) : TacticM Unit := do
  let snapshot ← snapshotFor rootStx { kernelCheck := false }
  unless snapshot.status == .saturated do
    throwError "distinct-witness extraction did not saturate"
  unless snapshot.facts.size == 4 && snapshot.witnesses.size == 2 do
    throwError "distinct-witness extraction returned the wrong fact or witness count"
  let first := snapshot.witnesses[0]!
  let second := snapshot.witnesses[1]!
  unless first.witness.id == 0 && second.witness.id == 1 &&
      first.witness.term != second.witness.term do
    throwError "distinct existential proofs were merged into one witness identity"
  unless first.factIndices == #[0, 1] && second.factIndices == #[2, 3] do
    throwError "facts were assigned to the wrong existential witness"
  unless existentialDepth snapshot.certificate.proposition == 2 do
    throwError "two distinct witnesses did not become two certificate binders"

private meta def guardFactBound (rootStx : Syntax) : TacticM Unit := do
  let snapshot ← snapshotFor rootStx {
    rootOnly := false, maxFacts := 0, kernelCheck := false
  }
  unless snapshot.status == .truncated && snapshot.facts.isEmpty && snapshot.witnesses.isEmpty do
    throwError "a fact-bound snapshot retained an uncertified or empty witness group"
  unless snapshot.certificate.proposition.isConstOf ``True do
    throwError "the empty snapshot certificate is not True"

private meta def guardRoundBound (rootStx ruleStx : Syntax) : TacticM Unit :=
    withMainContext do
  let root ← instantiateMVars (← Term.elabTerm rootStx none)
  let rule ← instantiateMVars (← Term.elabTerm ruleStx none)
  let snapshot ← wdykSnapshot root {
    hypotheses := #[rule], maxRounds := 0, rootOnly := false, kernelCheck := false
  }
  unless snapshot.status == .truncated do
    throwError "a productive zero-round extraction was reported as saturated"

private meta def guardZeroRoundFixpoint (rootStx : Syntax) : TacticM Unit := do
  let snapshot ← snapshotFor rootStx { maxRounds := 0, kernelCheck := false }
  unless snapshot.status == .saturated do
    throwError "a zero-round extraction already at a fixpoint was reported as truncated"

private meta def guardInconsistent (rootStx : Syntax) : TacticM Unit := do
  let snapshot ← snapshotFor rootStx { kernelCheck := false }
  unless snapshot.status == .inconsistent && snapshot.facts.isEmpty && snapshot.witnesses.isEmpty do
    throwError "inconsistent knowledge did not receive its distinct empty interpretation"
  unless snapshot.certificate.proposition.isConstOf ``False do
    throwError "an inconsistent snapshot did not carry a False certificate"
  kernelCheckClaim snapshot.scope snapshot.certificate.proposition snapshot.certificate.proof

private meta def guardScope (rootStx instanceStx : Syntax) : TacticM Unit :=
    withMainContext do
  let root ← instantiateMVars (← Term.elabTerm rootStx none)
  let instanceExpr ← instantiateMVars (← Term.elabTerm instanceStx none)
  let snapshot ← wdykSnapshot root { kernelCheck := false }
  unless root.isFVar && snapshot.scope.contains root.fvarId! do
    throwError "the snapshot did not retain the root's local declaration"
  unless instanceExpr.isFVar &&
      snapshot.localInstances.any (fun entry => entry.fvar == instanceExpr) do
    throwError "the snapshot did not retain its local instance cache"

syntax "guard_snapshot_shared " term : tactic
syntax "guard_snapshot_distinct " term : tactic
syntax "guard_snapshot_fact_bound " term : tactic
syntax "guard_snapshot_round_bound " term " via " term : tactic
syntax "guard_snapshot_zero_round_fixpoint " term : tactic
syntax "guard_snapshot_inconsistent " term : tactic
syntax "guard_snapshot_scope " term " with_instance " term : tactic

elab_rules : tactic
  | `(tactic| guard_snapshot_shared $root:term) => guardShared root
  | `(tactic| guard_snapshot_distinct $root:term) => guardDistinct root
  | `(tactic| guard_snapshot_fact_bound $root:term) => guardFactBound root
  | `(tactic| guard_snapshot_round_bound $root:term via $rule:term) => guardRoundBound root rule
  | `(tactic| guard_snapshot_zero_round_fixpoint $root:term) => guardZeroRoundFixpoint root
  | `(tactic| guard_snapshot_inconsistent $root:term) => guardInconsistent root
  | `(tactic| guard_snapshot_scope $root:term with_instance $localInstance:term) =>
      guardScope root localInstance

variable {Vertex : Type} (edge : Vertex → Vertex → Prop)

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  guard_snapshot_shared source
  trivial

example (source leftTarget rightTarget : Vertex)
    (leftRoute : ∃ middle, edge source middle ∧ edge middle leftTarget)
    (rightRoute : ∃ middle, edge source middle ∧ edge middle rightTarget) : True := by
  guard_snapshot_distinct source
  trivial

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  guard_snapshot_fact_bound source
  trivial

variable {P Q : Vertex → Prop}

example (source : Vertex) (known : P source) (step : ∀ x, P x → Q x) : True := by
  guard_snapshot_round_bound source via step
  trivial

example (source : Vertex) (known : P source) : True := by
  guard_snapshot_zero_round_fixpoint source
  trivial

example (source : Vertex) (known : P source) (refuted : ¬ P source) : True := by
  guard_snapshot_inconsistent source
  trivial

example {α : Type} [shown : ToString α] (value : α) : True := by
  guard_snapshot_scope value with_instance shown
  trivial

-- Default construction would bypass every guarantee, so none of the sealed runtime types may
-- acquire an `Inhabited` instance.
run_meta do
  for type in [mkConst ``Afaik, mkConst ``Inconsistency, mkConst ``WdykResult, mkConst ``Snapshot] do
    let inhabitedType ← mkAppM ``Inhabited #[type]
    if (← synthInstance? inhabitedType).isSome then
      throwError "a sealed extraction type has an Inhabited construction path"

-- Projection may leave gaps, but adding another witness must never recycle a surviving identity.
run_meta do
  let knowledge ← Afaik.empty (mkConst ``Bool.true)
  let knowledge ← knowledge.addWitness (mkConst ``Nat) (mkNatLit 0)
  let knowledge ← knowledge.addWitness (mkConst ``Nat) (mkNatLit 1)
  let knowledge := knowledge.project (fun _ => true) (fun witness => witness.id == 1)
  let knowledge ← knowledge.addWitness (mkConst ``Nat) (mkNatLit 2)
  unless knowledge.witnesses.map (·.id) == #[1, 2] do
    throwError "adding a witness after projection recycled a live identity"

/--
error: invalid {...} notation, constructor for `Snapshot` is marked as private
-/
#guard_msgs in
def cannotRewriteSnapshot (snapshot : Snapshot) : Snapshot :=
  { snapshot with status := .inconsistent }

/--
error: Unknown constant `Iykyk.Snapshot.mk`
-/
#guard_msgs in
#check Snapshot.mk

end Iykyk.Examples.Snapshot
