module

public import Iykyk.Extract

public section

/-!
# Consumer-neutral queries

This module is intentionally separate from extraction. Callers can query the same `RootedKnowledge`
that the pretty-printing tactic displays.

Academic lineage: constraint programming motivates querying accumulated knowledge before a concrete
value is available. See `README.md`.
-/

namespace Iykyk

open Lean Meta

/-- Return the fact whose proposition is definitionally equal to `proposition`, if one is known. -/
def findFact? (knowledge : RootedKnowledge) (proposition : Expr) : MetaM (Option KnownFact) := do
  for fact in knowledge.facts do
    let saved ← saveState
    let isMatch ← try isDefEq fact.proposition proposition catch _ => pure false
    saved.restore
    if isMatch then
      return some fact
  return none

/-- Whether the knowledge object contains a proof of `proposition`. Absence means unknown. -/
def knows (knowledge : RootedKnowledge) (proposition : Expr) : MetaM Bool := do
  return (← findFact? knowledge proposition).isSome

end Iykyk
