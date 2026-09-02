module

public import Iykyk.Extract
public import Lean.Elab.Tactic.Omega

public section

/-!
# Consumer-neutral queries

This module is intentionally separate from extraction. Callers can query the same `Afaik` that the
pretty-printing tactic displays, or ask a selected proof-producing mechanism to attempt one
specific proposition. Goal-directed queries never add consequences to the finite snapshot.

Academic lineage: constraint programming motivates querying accumulated knowledge before a concrete
value is available. See `README.md`.
-/

namespace Iykyk

open Lean Meta

/-- A proof-producing mechanism available to a focused query. -/
inductive ProofMechanism where
  /-- Simplify the goal using the active simp set and the facts in the `Afaik`. -/
  | simp
  /-- Prove Presburger arithmetic goals over `Nat` and `Int`. -/
  | omega
  deriving Inhabited, BEq, Repr

/-- Bounds and mechanism policy for a goal-directed proof query. -/
structure ProveConfig where
  /-- Mechanisms to try, in order. Direct lookup in the `Afaik` always happens first. -/
  mechanisms : Array ProofMechanism := #[]
  /-- When set, `simp` uses only these rules and the facts in the `Afaik`. -/
  simpOnlyRules : Option (Array Expr) := none
  /--
  Deterministic heartbeat budget for the complete mechanism phase, in Lean's user-facing units.
  Zero skips automation and reports `truncated`; exact fact lookup is still permitted.
  -/
  maxHeartbeats : Nat := 20_000
  /-- Have Lean's kernel check each proof before it crosses the query boundary. -/
  kernelCheck : Bool := true
  deriving Inhabited

/--
The result of a bounded proof query. `notProved` is deliberately weaker than "not derivable": the
selected mechanisms did not find a proof. `truncated` means the query exhausted or was given no
automation budget.
-/
inductive ProveResult where
  | proved (fact : KnownFact)
  | notProved
  | truncated
  deriving Inhabited

/-- Return the fact whose proposition is definitionally equal to `proposition`, if one is known. -/
def findFact? (knowledge : Afaik) (proposition : Expr) : MetaM (Option KnownFact) := do
  withLCtx knowledge.scope knowledge.localInstances do
    for fact in knowledge.facts do
      let saved ← saveState
      let isMatch ← try isDefEq fact.proposition proposition catch _ => pure false
      saved.restore
      if isMatch then
        return some fact
    return none

/-- Whether the knowledge object contains a proof of `proposition`. Absence means unknown. -/
def knows (knowledge : Afaik) (proposition : Expr) : MetaM Bool := do
  return (← findFact? knowledge proposition).isSome

private def addSimpRule (theorems : SimpTheorems) (index : Nat) (rule : Expr) :
    MetaM SimpTheorems := do
  let rule ← instantiateMVars rule
  if rule.isConst then
    let declaration ← getConstInfo rule.constName!
    if ← isProp declaration.type then
      theorems.addConst rule.constName!
    else
      theorems.addDeclToUnfold rule.constName!
  else
    theorems.add (.other (Name.mkSimple s!"iykyk.query.simp.{index}")) #[] rule

private def mkQuerySimpContext (knowledge : Afaik) (config : ProveConfig) :
    MetaM (Simp.Context × Simp.SimprocsArray) := do
  let mut theorems ← match config.simpOnlyRules with
    | none => getSimpTheorems
    | some _ => do
        let mut only : SimpTheorems := {}
        for builtin in [``eq_self, ``iff_self] do
          only ← only.addConst builtin
        pure only
  if let some rules := config.simpOnlyRules then
    for index in [:rules.size] do
      theorems ← addSimpRule theorems index rules[index]!
  let offset := config.simpOnlyRules.map (·.size) |>.getD 0
  for index in [:knowledge.facts.size] do
    theorems ← addSimpRule theorems (offset + index) knowledge.facts[index]!.proof
  let context ← Simp.mkContext
    (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let simprocs ← match config.simpOnlyRules with
    | none => pure #[(← Simp.getSimprocs)]
    | some _ => pure #[]
  return (context, simprocs)

private def finishProof (knowledge : Afaik) (goal proof : Expr) (config : ProveConfig) :
    MetaM KnownFact := do
  let goal ← instantiateMVars goal
  let proof ← instantiateMVars proof
  if goal.hasMVar || goal.hasLevelMVar || proof.hasMVar || proof.hasLevelMVar then
    throwError "iykyk: a proof query produced a result containing metavariables"
  checkEvidence goal proof
  if config.kernelCheck then
    kernelCheckClaim knowledge.scope goal proof
  return { proposition := goal, proof }

private def proveBySimp? (knowledge : Afaik) (goal : Expr) (config : ProveConfig) :
    MetaM (Option Expr) := do
  let saved ← saveState
  try
    let (context, simprocs) ← mkQuerySimpContext knowledge config
    let (result, _) ← simp goal context simprocs
    unless ← isDefEq result.expr (mkConst ``True) do
      saved.restore
      return none
    let proof ← instantiateMVars (← result.mkEqMPR (mkConst ``True.intro))
    return some proof
  catch _ =>
    saved.restore
    return none

private def introducedHypotheses (scope : LocalContext) : MetaM (List Expr) := do
  let mut result := []
  for hypothesis in ← getLocalHyps do
    if !scope.contains hypothesis.fvarId! then
      result := hypothesis :: result
  return result.reverse

private def proveByOmega? (knowledge : Afaik) (goal : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let target ← mkFreshExprSyntheticOpaqueMVar goal
    if let some contradictionGoal ← target.mvarId!.falseOrByContra then
      contradictionGoal.withContext do
        let facts := knowledge.facts.toList.map (·.proof) ++
          (← introducedHypotheses knowledge.scope)
        Lean.Elab.Tactic.Omega.omega facts contradictionGoal
    let proof ← instantiateMVars target
    if proof.hasMVar || proof.hasLevelMVar then
      saved.restore
      return none
    return some proof
  catch _ =>
    saved.restore
    return none

private def proveWithMechanisms (knowledge : Afaik) (goal : Expr) (config : ProveConfig) :
    MetaM ProveResult := do
  let mut attempted : Array ProofMechanism := #[]
  for mechanism in config.mechanisms do
    if attempted.contains mechanism then
      continue
    attempted := attempted.push mechanism
    let proof? ← match mechanism with
      | .simp => proveBySimp? knowledge goal config
      | .omega => proveByOmega? knowledge goal
    if let some proof := proof? then
      return .proved (← finishProof knowledge goal proof config)
  return .notProved

private def runWithQueryBudget (config : ProveConfig) (action : MetaM ProveResult) :
    MetaM ProveResult := do
  if config.maxHeartbeats == 0 then
    return .truncated
  withTheReader Core.Context
      (fun context => { context with maxHeartbeats := config.maxHeartbeats * 1000 }) do
    withCurrHeartbeats action

/--
Try to prove one proposition from an `Afaik`. Exact lookup is followed by the explicitly selected
mechanisms. The query runs in the captured local context, is bounded by `maxHeartbeats`, restores
all metavariable and elaborator state on every return path, and kernel-checks successful proofs by
default.
-/
def prove (knowledge : Afaik) (goal : Expr) (config : ProveConfig := {}) : MetaM ProveResult := do
  let saved ← saveState
  let action := withLCtx knowledge.scope knowledge.localInstances do
    unless ← isProp goal do
      throwError "iykyk: a proof query goal must be a proposition{indentExpr goal}"
    if let some fact ← findFact? knowledge goal then
      return .proved (← finishProof knowledge goal fact.proof config)
    if config.mechanisms.isEmpty then
      return .notProved
    runWithQueryBudget config (proveWithMechanisms knowledge goal config)
  let result ← tryCatchRuntimeEx action fun exception => do
    saved.restore
    if exception.isMaxHeartbeat then
      return .truncated
    throw exception
  saved.restore
  return result

/--
Convenient optional form of `prove`. Use `prove` when the caller must distinguish an exhausted
budget from a completed unsuccessful search.
-/
def prove? (knowledge : Afaik) (goal : Expr)
    (mechanisms : Array ProofMechanism := #[])
    (simpOnlyRules : Option (Array Expr) := none)
    (maxHeartbeats : Nat := 20_000)
    (kernelCheck : Bool := true) : MetaM (Option KnownFact) := do
  match ← prove knowledge goal { mechanisms, simpOnlyRules, maxHeartbeats, kernelCheck } with
  | .proved fact => return some fact
  | .notProved | .truncated => return none

end Iykyk
