module

public import Iykyk
meta import Iykyk

public section

/-!
# Goal-directed query tests

These tests exercise exact lookup, simp and omega proofs, negative answers, deterministic
truncation, kernel checking, and rollback of metavariable assignments.
-/

namespace Iykyk.Examples.Query

open Lean Meta Elab Tactic

set_option linter.unusedVariables false

private meta def extractedKnowledge (rootStx : Syntax) : TacticM Afaik := do
  let root ← instantiateMVars (← Term.elabTerm rootStx none)
  match ← wdyk root { rootOnly := false } with
  | .afaik knowledge => return knowledge
  | .inconsistent _ => throwError "query test unexpectedly extracted an inconsistent context"

private meta def elaboratedGoal (goalStx : Syntax) : TacticM Expr := do
  let goal ← instantiateMVars (← Term.elabTerm goalStx none)
  unless ← isProp goal do
    throwErrorAt goalStx "query test expected a proposition"
  return goal

private meta def assertProved (rootStx goalStx : Syntax)
    (mechanism : Option ProofMechanism) : TacticM Unit := withMainContext do
  let knowledge ← extractedKnowledge rootStx
  let goal ← elaboratedGoal goalStx
  let mechanisms := mechanism.map (#[·]) |>.getD #[]
  match ← prove knowledge goal { mechanisms } with
  | .proved fact =>
      checkEvidence goal fact.proof
      unless (← prove? knowledge goal (mechanisms := mechanisms)).isSome do
        throwErrorAt goalStx "the optional query API lost a successful proof"
  | .notProved => throwErrorAt goalStx "query unexpectedly failed to prove the goal"
  | .truncated => throwErrorAt goalStx "query unexpectedly exhausted its budget"

private meta def assertNotProved (rootStx goalStx : Syntax) : TacticM Unit :=
    withMainContext do
  let knowledge ← extractedKnowledge rootStx
  let goal ← elaboratedGoal goalStx
  match ← prove knowledge goal { mechanisms := #[.omega] } with
  | .notProved => return ()
  | .proved _ => throwErrorAt goalStx "query unexpectedly proved the goal"
  | .truncated => throwErrorAt goalStx "negative query unexpectedly exhausted its budget"

private meta def assertTruncated (rootStx goalStx : Syntax) : TacticM Unit := withMainContext do
  let knowledge ← extractedKnowledge rootStx
  let goal ← elaboratedGoal goalStx
  match ← prove knowledge goal { mechanisms := #[.omega], maxHeartbeats := 1 } with
  | .truncated => return ()
  | .proved _ => throwErrorAt goalStx "tiny-budget query unexpectedly proved the goal"
  | .notProved => throwErrorAt goalStx "tiny-budget query did not report truncation"

private meta def assertScopeFactNotUsed (rootStx goalStx : Syntax) : TacticM Unit :=
    withMainContext do
  let root ← instantiateMVars (← Term.elabTerm rootStx none)
  let goal ← elaboratedGoal goalStx
  let scope ← instantiateLCtxMVars (← getLCtx)
  let knowledge := Afaik.empty root scope (← getLocalInstances)
  match ← prove knowledge goal { mechanisms := #[.omega] } with
  | .notProved => return ()
  | .proved _ => throwErrorAt goalStx "query used a scope hypothesis absent from the Afaik"
  | .truncated => throwErrorAt goalStx "scope-isolation query unexpectedly exhausted its budget"

syntax "guard_iykyk_exact " term " proves " term : tactic
syntax "guard_iykyk_simp " term " proves " term : tactic
syntax "guard_iykyk_omega " term " proves " term : tactic
syntax "guard_iykyk_not_proved " term " fails " term : tactic
syntax "guard_iykyk_truncated " term " on " term : tactic
syntax "guard_iykyk_scope_isolated " term " from " term : tactic

elab_rules : tactic
  | `(tactic| guard_iykyk_exact $root:term proves $goal:term) =>
      assertProved root goal none
  | `(tactic| guard_iykyk_simp $root:term proves $goal:term) =>
      assertProved root goal (some .simp)
  | `(tactic| guard_iykyk_omega $root:term proves $goal:term) =>
      assertProved root goal (some .omega)
  | `(tactic| guard_iykyk_not_proved $root:term fails $goal:term) =>
      assertNotProved root goal
  | `(tactic| guard_iykyk_truncated $root:term on $goal:term) =>
      assertTruncated root goal
  | `(tactic| guard_iykyk_scope_isolated $root:term from $goal:term) =>
      assertScopeFactNotUsed root goal

example (a b : Nat) (known : a ≤ b) : True := by
  guard_iykyk_exact a proves a ≤ b
  trivial

example (a b : Nat) (f : Nat → Nat) (equal : a = b) : True := by
  guard_iykyk_simp a proves f a = f b
  trivial

example (a b c : Nat) (ha : a = b + 1) (hbc : b = c) : True := by
  guard_iykyk_omega a proves b ≤ a
  guard_iykyk_omega a proves a = c + 1
  guard_iykyk_omega a proves c < a + 1
  trivial

example (a b : Int) (difference : a = b - 3) : True := by
  guard_iykyk_omega a proves a < b
  trivial

example (a b : Nat) : True := by
  guard_iykyk_not_proved a fails a ≤ b
  guard_iykyk_truncated a on a ≤ b
  trivial

example (a b : Nat) (notExtracted : a ≤ b) : True := by
  guard_iykyk_scope_isolated a from a ≤ b
  trivial

-- Failed definitional matching must not leave a partial assignment behind.
run_meta do
  let knowledge := Afaik.empty (mkNatLit 0) (← getLCtx)
  let zeroEqualsZero ← mkEqRefl (mkNatLit 0)
  let proposition ← mkEq (mkNatLit 0) (mkNatLit 0)
  let knowledge ← knowledge.addFact proposition zeroEqualsZero
  let unknown ← mkFreshExprMVar (some (mkConst ``Nat))
  let goal ← mkEq unknown (mkNatLit 1)
  match ← prove knowledge goal with
  | .notProved => pure ()
  | _ => throwError "a deliberately unmatched query returned the wrong status"
  if ← unknown.mvarId!.isAssigned then
    throwError "a failed query leaked a metavariable assignment"

end Iykyk.Examples.Query
