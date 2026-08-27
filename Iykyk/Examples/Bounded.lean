module

public import Iykyk

public section

/-!
# Productive-rule and inconsistency examples
-/

namespace Iykyk.Examples.Bounded

set_option linter.unusedVariables false

variable {Vertex : Type}
variable (Reach : Vertex → Prop)

example (start : Vertex) (next : Vertex → Vertex)
    (seed : Reach start) (step : ∀ x, Reach x → Reach (next x)) : True := by
  iykyk start using [step]
  trivial

example (start : Vertex) (positive : Reach start) (negative : ¬ Reach start) : True := by
  iykyk start
  trivial

end Iykyk.Examples.Bounded
