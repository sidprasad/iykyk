module

public import Iykyk.Certify

public section

/-!
# The snapshot contract at runtime

`metatheory/IykykMetatheory.lean` states the consumer contract `Γ ; root ⊢extract[policy] K`
over a semantic `Snapshot`: the selected root, finite checked facts, witness groups, the context in
which its terms are meaningful, and the status of the finite run. This module is the runtime side
of that contract. `WdykResult.snapshot` presents a finished extraction result in the same shape, so
the two can be read field by field:

| runtime `Iykyk.Snapshot`          | metatheory `Iykyk.Metatheory.Snapshot`            |
| --------------------------------- | ------------------------------------------------- |
| `root : Expr`                     | `root : World → Root`                             |
| `scope : LocalContext`            | the context index `Γ`                             |
| `facts : Array KnownFact`         | `facts : List (Fact World)`                       |
| `witnesses : Array WitnessGroup`  | `witnesses : List (WitnessGroup Γ)`               |
| `status : Status`                 | `status : Status`                                 |
| `certificate : KnownFact`         | `Snapshot.interp`, entailed by `Extracts.interp`  |

The adapter is a view. It constructs no new proof and forgets nothing checked: every fact still
carries the proof `Afaik.addFact` checked, every witness group still carries the term
`Afaik.addWitness` checked, and the certificate is the one proposition `Afaik.certificate` builds
and `wdyk` asks the kernel to check (`False` with its proof for an inconsistent result). Witness
groups are computed by occurrence: a fact belongs to a witness's group when its proposition
contains that witness's `Classical.choose` term, which is the runtime form of "refers to one
shared witness".

## The remaining boundary

What relates the two tables is not a theorem but the trusted reading named in
`metatheory/README.md`: a kernel-checked `Expr` in `scope` is a fact that holds in every world
compatible with `scope`. Under that reading, the snapshot of a `wdyk` result satisfies the
judgment `Extracts`, with the calculus rules for hypothesis decomposition and rule application,
`certify` for facts whose proofs come from `simp`, and `openExists` for each `Classical.choose`
witness. iykyk does not internalize that reading: it would require a model of Lean's type theory
and a reflection principle strong enough to imply Lean's own consistency. The per-run kernel check
is the operational form of law 1 (every fact has a proof checked under `Γ`), and one witness term
occurring in several facts is the operational form of law 2 (one shared witness).
-/

namespace Iykyk

open Lean Meta

/-- The outcome of one finite extraction. Mirrors `Iykyk.Metatheory.Status`. -/
inductive Status where
  /-- The configured finite run reached a fixpoint. This is not logical completeness. -/
  | saturated
  /-- A configured bound stopped the run before a fixpoint. -/
  | truncated
  /-- The context was found contradictory, so no ordinary knowledge is reported. -/
  | inconsistent
  deriving Inhabited, BEq, Repr, DecidableEq

/--
One shared unknown together with the facts that mention it. Mirrors
`Iykyk.Metatheory.WitnessGroup`, whose predicates correspond to the facts indexed here.
-/
structure WitnessGroup where
  witness : Witness
  /-- Indices into `Snapshot.facts` of the facts whose propositions contain the witness term. -/
  facts : Array Nat
  deriving Inhabited

/--
A finished extraction result in the shape of the semantic contract.

The constructor is private: a `Snapshot` is obtained only through `WdykResult.snapshot`, so
holding one is evidence that it was derived from a checked `Afaik` or `Inconsistency`.
-/
structure Snapshot where
  private mk ::
  root : Expr
  /-- The context in which `root`, the facts, the witnesses, and the certificate are meaningful. -/
  scope : LocalContext
  facts : Array KnownFact
  witnesses : Array WitnessGroup
  status : Status
  /--
  The single proposition the snapshot expresses, with its proof: the facts conjoined and each
  witness bound once, or `False` for an inconsistent result. Its semantic counterpart is
  `Iykyk.Metatheory.Snapshot.interp`.
  -/
  certificate : KnownFact
  deriving Inhabited

/-- Whether `proposition` mentions `term`. -/
private def mentions (proposition term : Expr) : Bool :=
  proposition == term || (proposition.find? (· == term)).isSome

/-- Group the facts of a knowledge value by the witnesses they mention. -/
private def witnessGroups (knowledge : Afaik) : Array WitnessGroup :=
  knowledge.witnesses.map fun witness => {
    witness
    facts := (Array.range knowledge.facts.size).filter fun index =>
      mentions knowledge.facts[index]!.proposition witness.term
  }

/-- Present ordinary knowledge as a snapshot. Runs in the knowledge's own scope. -/
def Afaik.snapshot (knowledge : Afaik) : MetaM Snapshot :=
  withLCtx knowledge.scope knowledge.localInstances do
    return {
      root := knowledge.root
      scope := knowledge.scope
      facts := knowledge.facts
      witnesses := witnessGroups knowledge
      status := if knowledge.truncated then .truncated else .saturated
      certificate := ← knowledge.certificate
    }

/-- Present a checked contradiction as a snapshot: no facts, no witnesses, `False` certified. -/
def Inconsistency.snapshot (inconsistency : Inconsistency) : Snapshot where
  root := inconsistency.root
  scope := inconsistency.scope
  facts := #[]
  witnesses := #[]
  status := .inconsistent
  certificate := { proposition := mkConst ``False, proof := inconsistency.proof }

/-- The adapter from a finished extraction result to the snapshot contract. -/
def WdykResult.snapshot : WdykResult → MetaM Snapshot
  | .afaik knowledge => knowledge.snapshot
  | .inconsistent inconsistency => pure inconsistency.snapshot

end Iykyk
