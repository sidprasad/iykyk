module

public import Iykyk.Knowledge

public section

/-!
# Kernel certification of extraction results

A `RootedKnowledge` stores one proof per fact, each checked at insertion time by the elaborator.
This module builds the single proposition the whole knowledge value expresses — the design
document's `⟦K⟧ₜ` — and checks its combined proof with Lean's kernel in the captured
scope:

* the facts are conjoined in order, and
* each existential witness is abstracted back into an existential quantifier, innermost witness
  first, so that a witness shared by several facts becomes one bound variable with structural
  sharing rather than a repeated `Classical.choose` term.

For the running graph example the certificate proposition is literally
`∃ w, edge source w ∧ edge w target`, and `Lean.Kernel.check` — the kernel itself, not the
elaborator's definitional-equality test — accepts its proof on every extraction. This turns
the central contract `Γ ⊨ ⟦K⟧ₜ` from a statement about the implementation into a check the
kernel performs per run.

The kernel does not support metavariables or free universe parameters, so certification requires a
fully elaborated scope; extraction inside a universe-polymorphic section over `Sort u` would need
`kernelCheck := false`.
-/

namespace Iykyk

open Lean Meta

/-- Conjoin the facts of a knowledge value into one proposition with one proof. -/
private def conjunctionOf (facts : Array KnownFact) : MetaM KnownFact := do
  if facts.isEmpty then
    return { proposition := mkConst ``True, proof := mkConst ``True.intro }
  let mut result := facts.back!
  for offset in [1:facts.size] do
    let fact := facts[facts.size - 1 - offset]!
    result := {
      proposition := mkApp2 (mkConst ``And) fact.proposition result.proposition
      proof := mkApp4 (mkConst ``And.intro)
        fact.proposition result.proposition fact.proof result.proof
    }
  return result

/--
The single proposition expressed by a knowledge value, with its proof: the conjunction of all
facts, with every witness that still occurs abstracted into an existential quantifier. Witness
sharing is structural in the result — one binder, several occurrences.
-/
def RootedKnowledge.certificate (knowledge : RootedKnowledge) : MetaM KnownFact := do
  let mut result ← conjunctionOf knowledge.facts
  for witness in knowledge.witnesses.reverse do
    let term ← instantiateMVars witness.term
    let type ← instantiateMVars witness.type
    let body ← kabstract result.proposition term
    unless body.hasLooseBVars do
      -- The witness no longer occurs (e.g. its facts were projected away); an empty binder
      -- would add nothing to the certificate.
      continue
    let predicate := Expr.lam (Name.mkSimple s!"w{witness.id}") type body .default
    let proposition ← mkAppM ``Exists #[predicate]
    let proof ← mkAppOptM ``Exists.intro
      #[some type, some predicate, some term, some result.proof]
    result := { proposition, proof }
  return result

/--
Ask the kernel — not the elaborator — whether `evidence` proves `claim` in `scope`. The
claim and evidence are combined as `@id claim evidence`, so one kernel call checks both that
the claim is a well-formed proposition and that the evidence has exactly that type.
-/
def kernelCheckClaim (scope : LocalContext) (claim evidence : Expr) : MetaM Unit := do
  let checked ← instantiateMVars (mkApp2 (mkConst ``id [.zero]) claim evidence)
  if checked.hasMVar || checked.hasLevelMVar then
    throwError "iykyk: kernel certification requires a metavariable-free certificate\
      {indentExpr checked}"
  match Kernel.check (← getEnv) scope checked with
  | .ok _ => return ()
  | .error exception =>
      throwError "iykyk: kernel rejected the extraction certificate\n\
        {exception.toMessageData (← getOptions)}"

/-- Build the combined certificate and have the kernel check it in the captured scope. -/
def RootedKnowledge.kernelCertify (knowledge : RootedKnowledge) : MetaM KnownFact := do
  let certificate ← knowledge.certificate
  kernelCheckClaim knowledge.scope certificate.proposition certificate.proof
  return certificate

/-- Have the kernel check the contradiction proof in the captured scope. -/
def Inconsistency.kernelCertify (inconsistency : Inconsistency) : MetaM Unit :=
  kernelCheckClaim inconsistency.scope (mkConst ``False) inconsistency.proof

/-- Kernel-check whichever certificate an extraction result carries. -/
def ExtractionResult.kernelCertify : ExtractionResult → MetaM Unit
  | .knowledge value => discard value.kernelCertify
  | .inconsistent value => value.kernelCertify

end Iykyk
