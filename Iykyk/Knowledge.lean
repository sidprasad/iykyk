module

public import Lean

public section

/-!
# Proof-backed partial knowledge

The structures in this module are the consumer boundary. Expressions and proofs are meaningful in
the captured `LocalContext`. Existential witnesses use stable choice terms, so one unknown can occur
in more than one fact without introducing an unsafe free variable.

Academic lineage: incomplete relational databases motivate preserving unknown identity and treating
missing facts as unknown, not false. See the "Academic lineage" section in `README.md`.
-/

namespace Iykyk

open Lean

abbrev WitnessId := Nat

/-- A proposition paired with a kernel-checkable proof. -/
structure KnownFact where
  proposition : Expr
  proof : Expr
  deriving Inhabited

/-- An opt-in proof-producing engine used to refine or establish candidate facts. -/
inductive ProofEngine where
  | simp
  | aesop
  deriving Inhabited, BEq, Repr

/-- A shared unknown exposed from an existential proof. -/
structure Witness where
  id : WitnessId
  type : Expr
  term : Expr
  deriving Inhabited

/--
Finite knowledge rooted at one selected expression.

`scope` is part of the certificate: it is the context in which `root`, facts, and proofs are valid.
Witness terms themselves are scoped `Classical.choose` applications rather than new free variables.
-/
structure RootedKnowledge where
  root : Expr
  scope : LocalContext
  witnesses : Array Witness
  facts : Array KnownFact
  truncated : Bool
  deriving Inhabited

/-- Inconsistency is kept distinct from ordinary knowledge to avoid displaying arbitrary facts. -/
inductive ExtractionResult where
  | knowledge (value : RootedKnowledge)
  | inconsistent (root : Expr) (scope : LocalContext) (proof : Expr)
  deriving Inhabited

/-- Bounds and relevance policy for extraction. -/
structure Config where
  rules : Array Expr := #[]
  candidates : Array Expr := #[]
  engines : Array ProofEngine := #[]
  maxAesopRuleApplications : Nat := 200
  maxRounds : Nat := 4
  maxFacts : Nat := 128
  rootOnly : Bool := true
  deriving Inhabited

end Iykyk
