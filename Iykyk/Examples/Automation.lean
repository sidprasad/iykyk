module

public import Iykyk

public section

/-!
# Opt-in automation examples

These examples exercise the small user-facing hooks: explicit simp policies, raw or established
forward rules, and Aesop searches for named propositions (plus `False` for inconsistency).
-/

namespace Iykyk.Examples.Automation

set_option linter.unusedVariables false

variable {Vertex : Type}

inductive Shape where
  | leaf (label : Nat)
  | node (label : Nat)

/--
info: iykyk
  root: source
  witnesses: (none)
  facts:
    [0] Shape.leaf source = Shape.node source
  certificate: Shape.leaf source = Shape.node source
  status: complete
-/
#guard_msgs in
example (source : Nat) (impossible : Shape.leaf source = Shape.node source) : True := by
  iykyk source
  trivial

/--
info: iykyk
  root: source
  under the hood: simp
  status: inconsistent
-/
#guard_msgs in
example (source : Nat) (impossible : Shape.leaf source = Shape.node source) : True := by
  iykyk source with [simp]
  trivial

/--
info: iykyk
  root: source
  under the hood: simp
  witnesses: (none)
  facts:
    [0] Shape.leaf source = Shape.node source → False
  certificate: Shape.leaf source = Shape.node source → False
  status: complete
-/
#guard_msgs in
example (source : Nat) : True := by
  iykyk source deriving [Shape.leaf source ≠ Shape.node source] with [simp]
  trivial

/--
info: iykyk
  root: source
  under the hood: simp only
  witnesses: (none)
  facts:
    [0] Shape.leaf source = Shape.node source
  certificate: Shape.leaf source = Shape.node source
  status: complete
-/
#guard_msgs in
example (source : Nat) (impossible : Shape.leaf source = Shape.node source) : True := by
  iykyk source with [simp only []]
  trivial

/--
info: iykyk
  root: source
  under the hood: simp only
  witnesses: (none)
  facts:
    [0] source.reverse.reverse = source
  certificate: source.reverse.reverse = source
  status: complete
-/
#guard_msgs in
example (source : List Nat) : True := by
  iykyk source deriving [source.reverse.reverse = source]
    with [simp only [List.reverse_reverse]]
  trivial

/--
info: iykyk
  root: source
  witnesses: (none)
  facts:
    [0] P source
  certificate: P source
  status: complete
-/
#guard_msgs in
example (source : Vertex) (P Q : Vertex → Prop)
    (present : P source) (step : ∀ value, P value → Q value) : True := by
  iykyk source
  trivial

/--
info: iykyk
  root: source
  under the hood: local rules
  witnesses: (none)
  facts:
    [0] P source
    [1] Q source
  certificate: P source ∧ Q source
  status: complete
-/
#guard_msgs in
example (source : Vertex) (P Q : Vertex → Prop)
    (present : P source) (step : ∀ value, P value → Q value) : True := by
  iykyk source using *
  trivial

/--
info: iykyk
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
  status: complete
-/
#guard_msgs in
example (x : Vertex) (P Q R : Vertex → Prop)
    (chain : (P x → Q x) ∧ (Q x → R x)) (present : P x) : True := by
  iykyk x using facts
  trivial

/--
info: iykyk
  root: x
  under the hood: established rules
  witnesses: (none)
  facts:
    [0] P x → Q x
    [1] Q x → P x
    [2] P x
    [3] Q x
  certificate: (P x → Q x) ∧ (Q x → P x) ∧ P x ∧ Q x
  status: complete
-/
#guard_msgs in
example (x : Vertex) (P Q : Vertex → Prop) (equiv : P x ↔ Q x) (present : P x) : True := by
  iykyk x using facts
  trivial

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
