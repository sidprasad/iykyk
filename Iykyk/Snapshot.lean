module

public import Iykyk.Certify

public section

/-!
# The snapshot contract at runtime

`metatheory/IykykMetatheory.lean` states the consumer contract over a semantic `Snapshot`: the
selected root, finite checked facts, witness groups, the context in which its terms are meaningful,
and the status of the finite run, with the validity judgment `ValidSnapshot` giving its laws. This
module is the runtime side of that contract. `WdykResult.snapshot` presents a finished extraction
result in the same shape, so the two can be read field by field:

| runtime `Iykyk.Snapshot`               | metatheory `Iykyk.Metatheory.Snapshot`                  |
| -------------------------------------- | ------------------------------------------------------- |
| `root : Expr`                          | `root : World → Root`                                   |
| `scope`, `localInstances`              | the context index `Γ`                                   |
| `facts : Array KnownFact`              | `facts : List (Fact World)`                             |
| `witnesses : Array WitnessGroup`       | `witnesses : List (WitnessGroup Γ)`                     |
| `status : Status`                      | `status : Status`                                       |
| `certificate : KnownFact`              | `Snapshot.interp`, entailed by `ValidSnapshot.interp`   |

The adapter constructs no new proof and forgets nothing checked: every fact still carries the
proof `Afaik.addFact` checked and every witness group still carries the term `Afaik.addWitness`
checked. Witness groups are computed by occurrence: a fact belongs to a witness's group when its
proposition contains that witness's `Classical.choose` term, which is the runtime form of "refers
to one shared witness".

The certificate is kernel-checked at this boundary, unconditionally. `wdyk` also checks it unless
`Config.kernelCheck` is off, but a consumer holding a `Snapshot` cannot see that configuration,
so the snapshot performs its own check rather than inherit a conditional one. For ordinary
knowledge the certificate is the proposition `Afaik.certificate` builds, the facts conjoined with
each witness bound once; for an inconsistent result it is `False` with its proof, matching
`Snapshot.interp`, which is `False` for an inconsistent snapshot.

## The remaining boundary

What relates the two tables is not a theorem but the trusted reading named in
`metatheory/README.md`: a kernel-checked `Expr` in `scope` is a fact that holds in every world
compatible with `scope`. Under that reading, the snapshot of a `wdyk` result satisfies
`ValidSnapshot`, with the calculus rules for hypothesis decomposition and rule application,
`certify` for facts whose proofs come from `simp`, and `openExists` for each `Classical.choose`
witness. iykyk does not internalize that reading: it would require a model of Lean's type theory
and a reflection principle strong enough to imply Lean's own consistency. Nor does the runtime
produce a trace that would instantiate the judgment rule by rule; that is per-fact provenance,
issue #3. The kernel check here is the operational form of fact soundness, and one witness term
occurring in several facts is the operational form of witness sharing.
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

The constructor is private and there is no `Inhabited` instance. A `Snapshot` is obtained only
through `WdykResult.snapshot`, so holding one is evidence that it was derived from a checked
`Afaik` or `Inconsistency` and that its certificate was accepted by the kernel in its scope.
-/
structure Snapshot where
  private mk ::
  root : Expr
  /-- The context in which `root`, the facts, the witnesses, and the certificate are meaningful. -/
  scope : LocalContext
  /-- Typeclass instances registered in `scope`, needed when a consumer re-enters it. -/
  localInstances : LocalInstances
  facts : Array KnownFact
  witnesses : Array WitnessGroup
  status : Status
  /--
  The single proposition the snapshot expresses, with its proof, kernel-checked in `scope`: the
  facts conjoined and each witness bound once, or `False` for an inconsistent result. Its
  semantic counterpart is `Iykyk.Metatheory.Snapshot.interp`.
  -/
  certificate : KnownFact

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

/--
Present ordinary knowledge as a snapshot. Runs in the knowledge's own scope and has the kernel
check the combined certificate there.
-/
def Afaik.snapshot (knowledge : Afaik) : MetaM Snapshot :=
  withLCtx knowledge.scope knowledge.localInstances do
    return {
      root := knowledge.root
      scope := knowledge.scope
      localInstances := knowledge.localInstances
      facts := knowledge.facts
      witnesses := witnessGroups knowledge
      status := if knowledge.truncated then .truncated else .saturated
      certificate := ← knowledge.kernelCertify
    }

/--
Present a checked contradiction as a snapshot: no facts, no witnesses, and `False` as the
certificate, checked by the kernel in the contradiction's scope.
-/
def Inconsistency.snapshot (inconsistency : Inconsistency) : MetaM Snapshot := do
  inconsistency.kernelCertify
  return {
    root := inconsistency.root
    scope := inconsistency.scope
    localInstances := inconsistency.localInstances
    facts := #[]
    witnesses := #[]
    status := .inconsistent
    certificate := { proposition := mkConst ``False, proof := inconsistency.proof }
  }

/-- The adapter from a finished extraction result to the snapshot contract. -/
def WdykResult.snapshot : WdykResult → MetaM Snapshot
  | .afaik knowledge => knowledge.snapshot
  | .inconsistent inconsistency => inconsistency.snapshot

end Iykyk
