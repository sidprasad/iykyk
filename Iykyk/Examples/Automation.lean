module

public import Iykyk

public section

/-!
# Opt-in automation examples

These examples exercise the small user-facing hooks. `simp` normalizes established facts, while
Aesop searches only for propositions the caller names (plus `False` for inconsistency detection).
-/

namespace Iykyk.Examples.Automation

set_option linter.unusedVariables false

variable {Vertex : Type}

example (source target : List Nat) (edge : List Nat → List Nat → Prop)
    (route : edge source target.reverse.reverse) : True := by
  iykyk source with [simp]
  trivial

example (source : Nat) : True := by
  iykyk source deriving [source + 0 = source] with [simp]
  trivial

example (source left right : Vertex) (edge : Vertex → Vertex → Prop)
    (Reachable : Vertex → Prop)
    (choice : edge source left ∨ edge source right)
    (fromLeft : edge source left → Reachable source)
    (fromRight : edge source right → Reachable source) : True := by
  iykyk source deriving [Reachable source] with [aesop]
  trivial

example (source : Vertex) (P Q : Prop) (p : P) (forward : P → Q) (notQ : ¬ Q) : True := by
  iykyk source with [aesop]
  trivial

end Iykyk.Examples.Automation
