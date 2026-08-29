module

public import Iykyk.Knowledge

public section

/-!
# Opt-in proof-producing mechanisms

The extraction engine may ask standard `simp` or restricted `simp only` to normalize established
facts. The result crossing this module's boundary is an ordinary Lean proof term. The extraction
layer independently checks that proof before admitting the fact.

Academic lineage: proof-producing automation and proof-carrying code motivate treating automation
as an untrusted mechanism behind a small certificate boundary. See `README.md`.
-/

namespace Iykyk

open Lean Meta

/-- Whether a mechanism was explicitly enabled in this extraction configuration. -/
def Config.uses (config : Config) (mechanism : Via) : Bool :=
  config.mechanisms.contains mechanism

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

end Iykyk
