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

-- A chain of dependent resolutions: each resolved branch is the negation the next disjunction
-- needs. Resolution runs to a local fixpoint inside one saturation round, so the whole chain is
-- exposed regardless of its length, and the result is `complete` rather than bounded by
-- `maxRounds`.
/--
info: iykyk
  root: source
  witnesses: (none)
  facts:
    [0] A1 source → False
    [1] A1 source ∨ ¬A2 source
    [2] A2 source ∨ ¬A3 source
    [3] A3 source ∨ ¬A4 source
    [4] A4 source ∨ ¬A5 source
    [5] A5 source ∨ B source
    [6] A2 source → False
    [7] A3 source → False
    [8] A4 source → False
    [9] A5 source → False
    [10] B source
  certificate: (A1 source → False) ∧
  (A1 source ∨ ¬A2 source) ∧
    (A2 source ∨ ¬A3 source) ∧
      (A3 source ∨ ¬A4 source) ∧
        (A4 source ∨ ¬A5 source) ∧
          (A5 source ∨ B source) ∧
            (A2 source → False) ∧ (A3 source → False) ∧ (A4 source → False) ∧ (A5 source → False) ∧ B source
  status: complete
-/
#guard_msgs in
example (source : Vertex) (A1 A2 A3 A4 A5 B : Vertex → Prop)
    (n1 : ¬ A1 source)
    (d1 : A1 source ∨ ¬ A2 source) (d2 : A2 source ∨ ¬ A3 source)
    (d3 : A3 source ∨ ¬ A4 source) (d4 : A4 source ∨ ¬ A5 source)
    (d5 : A5 source ∨ B source) : True := by
  iykyk source
  trivial

end Iykyk.Examples.Logic
