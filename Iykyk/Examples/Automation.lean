module

public import Iykyk

public section

/-!
# Opt-in automation examples

These examples exercise the small user-facing hooks: explicit simp policies and selected or
established forward rules.
-/

namespace Iykyk.Examples.Automation

set_option linter.unusedVariables false

variable {Vertex : Type}

inductive Shape where
  | leaf (label : Nat)
  | node (label : Nat)

/--
info: afaik
  root: source
  witnesses: (none)
  facts:
    [0] Shape.leaf source = Shape.node source
  certificate: Shape.leaf source = Shape.node source
  status: saturated
-/
#guard_msgs in
example (source : Nat) (impossible : Shape.leaf source = Shape.node source) : True := by
  wdyk source
  trivial

/--
info: afaik
  root: source
  under the hood: simp
  status: inconsistent
-/
#guard_msgs in
example (source : Nat) (impossible : Shape.leaf source = Shape.node source) : True := by
  wdyk source via [simp]
  trivial

/--
info: afaik
  root: source
  under the hood: simp only
  witnesses: (none)
  facts:
    [0] Shape.leaf source = Shape.node source
  certificate: Shape.leaf source = Shape.node source
  status: saturated
-/
#guard_msgs in
example (source : Nat) (impossible : Shape.leaf source = Shape.node source) : True := by
  wdyk source via [simp only []]
  trivial

/--
info: afaik
  root: source
  witnesses: (none)
  facts:
    [0] P source
  certificate: P source
  status: saturated
-/
#guard_msgs in
example (source : Vertex) (P Q : Vertex → Prop)
    (present : P source) (step : ∀ value, P value → Q value) : True := by
  wdyk source
  trivial

/--
info: afaik
  root: source
  under the hood: established rules
  witnesses: (none)
  facts:
    [0] P source
    [1] Q source
  certificate: P source ∧ Q source
  status: saturated
-/
#guard_msgs in
example (source : Vertex) (P Q : Vertex → Prop)
    (present : P source) (step : ∀ value, P value → Q value) : True := by
  wdyk source fyi *
  trivial

/--
info: afaik
  root: x
  under the hood: established rules
  witnesses: (none)
  facts:
    [0] P x → Q x
    [1] Q x → R x
    [2] P x
    [3] Q x
    [4] R x
  certificate: (P x → Q x) ∧ (Q x → R x) ∧ P x ∧ Q x ∧ R x
  status: saturated
-/
#guard_msgs in
example (x : Vertex) (P Q R : Vertex → Prop)
    (chain : (P x → Q x) ∧ (Q x → R x)) (present : P x) : True := by
  wdyk x fyi *
  trivial

/--
info: afaik
  root: x
  under the hood: established rules
  witnesses: (none)
  facts:
    [0] P x → Q x
    [1] Q x → P x
    [2] P x
    [3] Q x
  certificate: (P x → Q x) ∧ (Q x → P x) ∧ P x ∧ Q x
  status: saturated
-/
#guard_msgs in
example (x : Vertex) (P Q : Vertex → Prop) (equiv : P x ↔ Q x) (present : P x) : True := by
  wdyk x fyi *
  trivial

/--
info: afaik
  root: x
  witnesses: (none)
  facts:
    [0] P x → Q x
    [1] Q x → P x
    [2] P x
    [3] Q x
  certificate: (P x → Q x) ∧ (Q x → P x) ∧ P x ∧ Q x
  status: saturated
-/
#guard_msgs in
example (x : Vertex) (P Q : Vertex → Prop) (equiv : P x ↔ Q x) (present : P x) : True := by
  wdyk x fyi [equiv]
  trivial

/--
info: afaik
  root: x
  witnesses: (none)
  facts:
    [0] P x → Q x
    [1] Q x → P x
    [2] Q x
    [3] P x
  certificate: (P x → Q x) ∧ (Q x → P x) ∧ Q x ∧ P x
  status: saturated
-/
#guard_msgs in
example (x : Vertex) (P Q : Vertex → Prop) (equiv : P x ↔ Q x) (present : Q x) : True := by
  wdyk x fyi [equiv]
  trivial

-- `fyi` accepts evidence, not an arbitrary value or an unproved proposition.
/--
error: `fyi` expects a proof of a proposition
-/
#guard_msgs in
example (source n : Nat) : True := by
  wdyk source fyi [n]
  trivial

example (source target : List Nat) (edge : List Nat → List Nat → Prop)
    (route : edge source target.reverse.reverse) : True := by
  wdyk source via [simp]
  trivial

end Iykyk.Examples.Automation
