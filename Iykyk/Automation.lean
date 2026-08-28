module

public import Iykyk.Knowledge
public import Aesop.BuiltinRules
import Aesop.Search.Main

public section

/-!
# Opt-in proof engines

The extraction engine may ask standard `simp`, restricted `simp only`, or Aesop to prove a named
candidate. Simp may also normalize established facts. In every mode, the result crossing this
module's boundary is an ordinary Lean proof term. The extraction layer independently checks that
proof before admitting the fact.

Academic lineage: proof-producing automation and proof-carrying code motivate treating automation
as an untrusted search mechanism behind a small certificate boundary. See `README.md`.
-/

namespace Iykyk

open Lean Meta

/-- Whether an engine was explicitly enabled in this extraction configuration. -/
def Config.uses (config : Config) (engine : ProofEngine) : Bool :=
  config.engines.contains engine

private def mkSimpOnlyContext (rules : Array Expr) : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  for builtin in [``eq_self, ``iff_self] do
    theorems ← theorems.addConst builtin
  for index in [:rules.size] do
    let rule ← instantiateMVars rules[index]!
    if rule.isConst then
      let declaration ← getConstInfo rule.constName!
      if ← isProp declaration.type then
        theorems ← theorems.addConst rule.constName!
      else
        theorems ← theorems.addDeclToUnfold rule.constName!
    else
      theorems ← theorems.add (.other (Name.mkSimple s!"iykyk.simpOnly.{index}")) #[] rule
  Simp.mkContext
    (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)

private def simpSetup (config : Config) : MetaM (Simp.Context × Simp.SimprocsArray) := do
  match config.simpOnlyRules with
  | none => return (← Simp.Context.mkDefault, #[(← Simp.getSimprocs)])
  | some rules => return (← mkSimpOnlyContext rules, #[])

/-- Normalize an established proposition with the selected simp policy, transporting its proof. -/
def simplifyProvedFact (proposition proof : Expr) (config : Config := {}) : MetaM KnownFact := do
  let proposition ← instantiateMVars proposition
  let proof ← instantiateMVars proof
  let (context, simprocs) ← simpSetup config
  let (result, _) ← simp proposition context simprocs
  return {
    proposition := ← instantiateMVars result.expr
    proof := ← instantiateMVars (← result.mkEqMP proof)
  }

private def proveBySimp (config : Config) (proposition : Expr) : MetaM (Option Expr) := do
  let (context, simprocs) ← simpSetup config
  let (result, _) ← simp proposition context simprocs
  let simplified ← whnf result.expr
  unless simplified.isConstOf ``True do
    return none
  match result.proof? with
  | some equality => return some (← mkOfEqTrue equality)
  | none => return some (mkConst ``True.intro)

private def proveByAesop (proposition : Expr) (maxRuleApplications : Nat) :
    MetaM (Option Expr) := do
  let saved ← saveState
  try
    let goalExpr ← mkFreshExprMVar (some proposition)
    let goal := goalExpr.mvarId!
    let options : Aesop.Options := {
      maxRuleApplications
      terminal := false
      warnOnNonterminal := false
    }
    let (goals, _) ← Aesop.search goal (options := options)
    let proof? ← if goals.isEmpty then
      let proof ← instantiateMVars goalExpr
      pure (if proof.hasMVar then none else some proof)
    else
      pure none
    saved.restore
    return proof?
  catch _ =>
    saved.restore
    return none

/-- Try enabled engines, in the requested order, and return the first proof they produce. -/
def proveCandidate (config : Config) (proposition : Expr) : MetaM (Option Expr) := do
  for engine in config.engines do
    let proof? ← match engine with
      | .simp => proveBySimp config proposition
      | .aesop => proveByAesop proposition config.maxAesopRuleApplications
    if let some proof := proof? then
      return some proof
  return none

end Iykyk
