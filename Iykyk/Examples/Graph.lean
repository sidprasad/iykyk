module

public import Iykyk

public section

/-!
# Shared-witness and derived-knowledge examples
-/

namespace Iykyk.Examples.Graph

set_option linter.unusedVariables false

variable {Vertex : Type}
variable (edge Reach : Vertex → Vertex → Prop)

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target) : True := by
  wdyk source
  trivial

example (source target : Vertex)
    (route : ∃ middle, edge source middle ∧ edge middle target)
    (step : ∀ x y, edge x y → Reach x y) : True := by
  wdyk source fyi [step]
  trivial

example (source left right : Vertex)
    (choice : edge source left ∨ edge source right) : True := by
  wdyk source
  trivial

end Iykyk.Examples.Graph
