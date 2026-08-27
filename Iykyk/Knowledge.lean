module

public import Lean

public section

/-!
# Proof-backed partial knowledge

The structures in this module are the consumer boundary. Expressions and proofs are meaningful in
the captured `LocalContext`. Existential witnesses use stable choice terms, so one unknown can occur
in more than one fact without introducing an unsafe free variable.

`RootedKnowledge` and `Inconsistency` have private constructors: the only way to build or change
one is through the smart constructors below, each of which either checks the supplied evidence or
performs an operation that cannot invalidate it (subset projection, setting the truncation flag).
These operations mirror, one for one, the operations proved sound in
`metatheory/IykykMetatheory.lean` (`CertifiedKnowledge.empty`/`add`/`project`/`withTruncated`), so
the metatheory constrains the implementation through the shape of this API, not just by
documentation.

Academic lineage: incomplete relational databases motivate preserving unknown identity and treating
missing facts as unknown, not false; LCF-style kernels motivate making certified values
unforgeable outside a small checked interface. See the "Academic lineage" section in `README.md`.
-/

namespace Iykyk

open Lean Meta

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
Check that `evidence` establishes `claim`: the inferred type of `evidence` must be definitionally
equal to `claim`. This is the fast elaborator-level gate used at every insertion; the final
extraction result is additionally checked by the kernel (see `Iykyk/Certify.lean`).
-/
def checkEvidence (claim evidence : Expr) : MetaM Unit := do
  let claimed ← whnf (← instantiateMVars claim)
  let established ← whnf (← instantiateMVars (← inferType evidence))
  unless ← isDefEq established claimed do
    throwError "iykyk internal error: evidence does not establish the extracted claim\n\
      claim: {claimed}\n  evidence type: {established}"

/--
Finite knowledge rooted at one selected expression.

`scope` is part of the certificate: it is the context in which `root`, facts, and proofs are valid.
Witness terms themselves are scoped `Classical.choose` applications rather than new free variables.

The constructor is private. A `RootedKnowledge` can only be grown from `RootedKnowledge.empty` by
`addFact` (which checks the proof), `addWitness` (which checks the term), `project` (which can only
delete), and `withTruncated` (which changes no semantic content). Holding a value of this type is
therefore evidence that every fact in it was checked against its proof.
-/
structure RootedKnowledge where
  private mk ::
  root : Expr
  scope : LocalContext
  witnesses : Array Witness
  facts : Array KnownFact
  truncated : Bool
  deriving Inhabited

/-- Empty knowledge about `root`, valid in `scope`. Mirrors `CertifiedKnowledge.empty`. -/
def RootedKnowledge.empty (root : Expr) (scope : LocalContext) : RootedKnowledge where
  root := root
  scope := scope
  witnesses := #[]
  facts := #[]
  truncated := false

/--
Add one fact, checking its proof first. Mirrors `CertifiedKnowledge.add`, whose certificate
argument corresponds to the check performed here. Callers must be in the knowledge's `scope`.
-/
def RootedKnowledge.addFact (knowledge : RootedKnowledge) (proposition proof : Expr) :
    MetaM RootedKnowledge := do
  let proposition ← instantiateMVars proposition
  let proof ← instantiateMVars proof
  if proposition.hasMVar || proof.hasMVar then
    throwError "iykyk internal error: fact may not contain metavariables{indentExpr proposition}"
  checkEvidence proposition proof
  return { knowledge with facts := knowledge.facts.push { proposition, proof } }

/-- Expose one shared unknown, checking that its term has the declared type. -/
def RootedKnowledge.addWitness (knowledge : RootedKnowledge) (type term : Expr) :
    MetaM RootedKnowledge := do
  let type ← instantiateMVars type
  let term ← instantiateMVars term
  checkEvidence type term
  return { knowledge with
    witnesses := knowledge.witnesses.push { id := knowledge.witnesses.size, type, term } }

/--
Keep only the selected facts and witnesses. Deletion cannot invalidate the remaining checked
facts; this mirrors `CertifiedKnowledge.project`, where the subset condition holds by construction
because `project` can only filter.
-/
def RootedKnowledge.project (knowledge : RootedKnowledge)
    (keepFact : KnownFact → Bool) (keepWitness : Witness → Bool) : RootedKnowledge :=
  { knowledge with
    facts := knowledge.facts.filter keepFact
    witnesses := knowledge.witnesses.filter keepWitness }

/-- Set the operational truncation flag. Mirrors `CertifiedKnowledge.withTruncated`. -/
def RootedKnowledge.withTruncated (knowledge : RootedKnowledge) (truncated : Bool) :
    RootedKnowledge :=
  { knowledge with truncated }

/--
A proved contradiction in `scope`. Kept distinct from ordinary knowledge because an inconsistent
context entails every proposition, so displaying arbitrary facts would be technically sound and
practically useless. The constructor is private; `Inconsistency.ofProof` checks the proof.
-/
structure Inconsistency where
  private mk ::
  root : Expr
  scope : LocalContext
  proof : Expr
  deriving Inhabited

/-- Package a checked proof of `False`. -/
def Inconsistency.ofProof (root : Expr) (scope : LocalContext) (proof : Expr) :
    MetaM Inconsistency := do
  let proof ← instantiateMVars proof
  if proof.hasMVar then
    throwError "iykyk internal error: contradiction proof may not contain metavariables"
  checkEvidence (mkConst ``False) proof
  return { root, scope, proof }

/-- Inconsistency is kept distinct from ordinary knowledge to avoid displaying arbitrary facts. -/
inductive ExtractionResult where
  | knowledge (value : RootedKnowledge)
  | inconsistent (value : Inconsistency)
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
  /--
  Re-check the final extraction result with Lean's kernel: the facts are conjoined, witnesses are
  abstracted back into existential quantifiers, and the resulting single certificate is checked by
  `Lean.Kernel.check` in the captured scope. Disable only for performance experiments; the
  per-insertion checks above remain in force either way.
  -/
  kernelCheck : Bool := true
  deriving Inhabited

end Iykyk
