module

public import Iykyk
meta import Iykyk

public section

/-!
# Certification tests

These tests pin down the enforcement layer rather than the extraction policy:

* the central graph example's output — including its kernel-checked certificate, in which the
  shared witness is one existential binder — is locked with `#guard_msgs`;
* a fact whose proof does not establish it is rejected by the smart-constructor boundary; and
* the kernel gate itself rejects a mismatched certificate, and accepts a correct one.
-/

namespace Iykyk.Examples.Certified

set_option linter.unusedVariables false

variable {Vertex : Type}
variable (edge : Vertex → Vertex → Prop)

/--
info: iykyk
  root: source
  witnesses:
    •0 : Vertex := Classical.choose route
  facts:
    [0] edge source (Classical.choose route)
    [1] edge (Classical.choose route) target
  certificate: ∃ w0, edge source w0 ∧ edge w0 target
  status: complete
-/
#guard_msgs in
example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  iykyk source
  trivial

-- A certificate extracted after a local proof has a fully instantiated scope,
-- so the combined certificate is accepted by the kernel.
example (source target middle : Vertex)
    (left : edge source middle) (right : edge middle target) : True := by
  have route : ∃ middle, edge source middle ∧ edge middle target :=
    ⟨middle, left, right⟩
  iykyk source
  trivial

open Lean Meta

-- `RootedKnowledge` is unforgeable: its constructor is private, and the only way to insert a
-- fact checks the proof. A proof of `True` must not certify `False`.
run_meta do
  let knowledge := RootedKnowledge.empty (mkConst ``Bool.true) (← getLCtx)
  let rejected ← try
      discard <| knowledge.addFact (mkConst ``False) (mkConst ``True.intro)
      pure false
    catch _ => pure true
  unless rejected do
    throwError "a fact with a mismatched proof was accepted"

-- The same boundary rejects a witness term whose type does not match its declaration.
run_meta do
  let knowledge := RootedKnowledge.empty (mkConst ``Bool.true) (← getLCtx)
  let rejected ← try
      discard <| knowledge.addWitness (mkConst ``Nat) (mkConst ``Bool.true)
      pure false
    catch _ => pure true
  unless rejected do
    throwError "a witness with a mismatched type was accepted"

-- The kernel gate rejects a mismatched certificate and accepts a correct one.
run_meta do
  let rejected ← try
      kernelCheckClaim (← getLCtx) (mkConst ``False) (mkConst ``True.intro)
      pure false
    catch _ => pure true
  unless rejected do
    throwError "the kernel accepted a proof of True as a certificate for False"
  kernelCheckClaim (← getLCtx) (mkConst ``True) (mkConst ``True.intro)

end Iykyk.Examples.Certified
