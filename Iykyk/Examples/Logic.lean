module

public import Iykyk

public section

/-!
# Core logical-rule examples

These examples pin the small proof-producing rules built into extraction itself. Caller-supplied
rules and opt-in proof engines are exercised separately in `Iykyk.Examples.Automation`.
-/

namespace Iykyk.Examples.Logic

set_option linter.unusedVariables false

variable {Vertex : Type}

/--
info: iykyk
  root: source
  witnesses: (none)
  facts:
    [0] A source → B source
    [1] B source → A source
  certificate: (A source → B source) ∧ (B source → A source)
  status: complete
-/
#guard_msgs in
example (source : Vertex) (A B : Vertex → Prop) (equivalence : A source ↔ B source) : True := by
  iykyk source
  trivial

/--
info: iykyk
  root: source
  witnesses: (none)
  facts:
    [0] A source ∨ B source
    [1] A source → False
    [2] B source
  certificate: (A source ∨ B source) ∧ (A source → False) ∧ B source
  status: complete
-/
#guard_msgs in
example (source : Vertex) (A B : Vertex → Prop)
    (choice : A source ∨ B source) (notA : ¬ A source) : True := by
  iykyk source
  trivial

example (source : Vertex) (A B : Vertex → Prop)
    (choice : A source ∨ B source) (notB : ¬ B source) : True := by
  iykyk source
  trivial

end Iykyk.Examples.Logic
