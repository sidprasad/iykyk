module

public import Iykyk

public section

/-!
# Excluding local hypotheses from extraction

`nvm [h]` ("nevermind") removes local hypotheses from a single extraction. An excluded declaration
is skipped during context collection, so its facts and witnesses never enter the knowledge and it
cannot form a relevance bridge, fire as a forward rule, or trigger contradiction detection. Unlike
`clear h`, it leaves the caller's proof state untouched.
-/

namespace Iykyk.Examples.Exclusion

set_option linter.unusedVariables false

variable {V : Type}

-- A relevance bridge, in miniature. Inspecting `left` normally reaches `r`, and therefore `P r`,
-- through the two `rel` steps: exactly the transitive connection the AVL motivation in issue #21
-- wants to cut for one query.
/--
info: afaik
  root: left
  witnesses: (none)
  facts:
    [0] rel left x
    [1] rel x r
    [2] P r
  certificate: rel left x ∧ rel x r ∧ P r
  status: saturated
-/
#guard_msgs in
example (left x r : V) (rel : V → V → Prop) (P : V → Prop)
    (bridgeL : rel left x) (bridge2 : rel x r) (hr : P r) : True := by
  wdyk left
  trivial

-- Excluding the middle step severs the bridge, so `r` and `P r` are no longer extracted.
/--
info: afaik
  root: left
  witnesses: (none)
  facts:
    [0] rel left x
  certificate: rel left x
  status: saturated
-/
#guard_msgs in
example (left x r : V) (rel : V → V → Prop) (P : V → Prop)
    (bridgeL : rel left x) (bridge2 : rel x r) (hr : P r) : True := by
  wdyk left nvm [bridge2]
  trivial

-- A rule supplied with `fyi` fires as usual, deriving `B source`.
/--
info: afaik
  root: source
  witnesses: (none)
  facts:
    [0] A source
    [1] B source
  certificate: A source ∧ B source
  status: saturated
-/
#guard_msgs in
example (source : V) (A B : V → Prop)
    (seed : A source) (step : ∀ x, A x → B x) : True := by
  wdyk source fyi [step]
  trivial

-- Precedence: exclusion wins over `fyi`. Naming the same declaration in both clauses drops it, so
-- the rule never fires and `B source` stays unknown.
/--
info: afaik
  root: source
  witnesses: (none)
  facts:
    [0] A source
  certificate: A source
  status: saturated
-/
#guard_msgs in
example (source : V) (A B : V → Prop)
    (seed : A source) (step : ∀ x, A x → B x) : True := by
  wdyk source fyi [step] nvm [step]
  trivial

-- With both a proposition and its negation in scope, extraction reports the inconsistency.
/--
info: afaik
  root: source
  status: inconsistent
-/
#guard_msgs in
example (source : V) (A : V → Prop) (pos : A source) (neg : ¬ A source) : True := by
  wdyk source
  trivial

-- Excluding the negation removes it from consideration, so the contradiction is not detected and
-- the remaining fact is reported normally.
/--
info: afaik
  root: source
  witnesses: (none)
  facts:
    [0] A source
  certificate: A source
  status: saturated
-/
#guard_msgs in
example (source : V) (A : V → Prop) (pos : A source) (neg : ¬ A source) : True := by
  wdyk source nvm [neg]
  trivial

-- Misuse: `nvm` identifies local declarations, so it rejects a non-local term.
/-- error: Unexpected term `A source`; expected single reference to variable -/
#guard_msgs in
example (source : V) (A : V → Prop) (ha : A source) : True := by
  wdyk source nvm [A source]
  trivial

end Iykyk.Examples.Exclusion
