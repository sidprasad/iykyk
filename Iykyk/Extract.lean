module

public import Iykyk.Automation
public import Iykyk.Certify

public section

/-!
# Certified extraction engine

This deliberately small engine decomposes conjunctions and existentials, applies explicit
Horn-style rules, asks opt-in engines about named candidates, detects contradictions, and optionally
keeps only facts connected to the selected root.

The engine never constructs a `RootedKnowledge` directly: it grows one through the checked smart
constructors in `Iykyk/Knowledge.lean`, so every inserted fact is checked against its proof at the
moment of insertion. Unless disabled in the configuration, the finished result is then re-checked
end to end by Lean's kernel (`Iykyk/Certify.lean`).

Academic lineage: the database chase motivates explicit forward rounds; abstract interpretation and
shape analysis motivate a sound finite result with a separate `truncated` bit. See `README.md`.
-/

namespace Iykyk

open Lean Meta

private structure BuildState where
  knowledge : RootedKnowledge
  hitFactLimit : Bool := false

private structure Candidate where
  proposition : Expr
  proof : Expr

private def normalize (e : Expr) : MetaM Expr := do
  whnf (← instantiateMVars e)

private def containsExpr (haystack needle : Expr) : Bool :=
  haystack == needle || (haystack.find? (· == needle)).isSome

private def factExists (facts : Array KnownFact) (proposition : Expr) : Bool :=
  facts.any fun fact => fact.proposition == proposition

private def pushFact (state : BuildState) (config : Config) (proposition proof : Expr) :
    MetaM BuildState := do
  let proposition ← normalize proposition
  if factExists state.knowledge.facts proposition then
    return state
  if state.knowledge.facts.size >= config.maxFacts then
    return { state with hitFactLimit := true }
  return { state with knowledge := ← state.knowledge.addFact proposition proof }

private def matchesKnownFact (facts : Array KnownFact) (proposition : Expr) : MetaM Bool := do
  for fact in facts do
    let saved ← saveState
    let matched ← try isDefEq fact.proposition proposition catch _ => pure false
    saved.restore
    if matched then
      return true
  return false

private partial def structurallyKnown (facts : Array KnownFact) (proposition : Expr) :
    MetaM Bool := do
  let proposition ← normalize proposition
  if proposition.isAppOfArity ``And 2 then
    let args := proposition.getAppArgs
    if !(← structurallyKnown facts args[0]!) then
      return false
    structurallyKnown facts args[1]!
  else
    matchesKnownFact facts proposition

/-- Whether an in-scope term already witnesses an existential's structurally decomposed body. -/
private def existentialAlreadyKnown (type predicate : Expr) (facts : Array KnownFact) :
    MetaM Bool := do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let candidate := Expr.fvar localDecl.fvarId
      let saved ← saveState
      let hasType ← try isDefEq (← inferType candidate) type catch _ => pure false
      saved.restore
      if hasType && (← structurallyKnown facts (mkApp predicate candidate)) then
        return true
  return false

private partial def decompose (config : Config) (proof proposition : Expr)
    (state : BuildState) : MetaM BuildState := do
  let fact ← if config.uses .simp then
    simplifyProvedFact proposition proof
  else
    pure { proposition, proof }
  let proposition ← normalize fact.proposition
  let proof ← instantiateMVars fact.proof
  if proposition.isAppOfArity ``And 2 then
    let args := proposition.getAppArgs
    let state ← decompose config (← mkAppM ``And.left #[proof]) args[0]! state
    decompose config (← mkAppM ``And.right #[proof]) args[1]! state
  else if proposition.isAppOfArity ``Iff 2 then
    let forward ← mkAppM ``Iff.mp #[proof]
    let state ← decompose config forward (← inferType forward) state
    let backward ← mkAppM ``Iff.mpr #[proof]
    decompose config backward (← inferType backward) state
  else if proposition.isAppOfArity ``Exists 2 then
    let args := proposition.getAppArgs
    if ← existentialAlreadyKnown args[0]! args[1]! state.knowledge.facts then
      return state
    let witnessTerm ← mkAppM ``Classical.choose #[proof]
    let state := { state with knowledge := ← state.knowledge.addWitness args[0]! witnessTerm }
    let specProof ← mkAppM ``Classical.choose_spec #[proof]
    decompose config specProof (← inferType specProof) state
  else
    pushFact state config proposition proof

private def collectContext (config : Config) (initial : BuildState) : MetaM BuildState := do
  let mut state := initial
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      if ← isProp localDecl.type then
        state ← decompose config (.fvar localDecl.fvarId) localDecl.type state
  return state

private partial def applyRuleCore (ruleProof ruleType : Expr)
    (facts : Array KnownFact) : MetaM (Array Candidate) := do
  let ruleType ← whnf ruleType
  match ruleType with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        let mut candidates := #[]
        for fact in facts do
          let saved ← saveState
          try
            if ← isDefEq domain fact.proposition then
              candidates := candidates ++ (← applyRuleCore
                (mkApp ruleProof fact.proof) (body.instantiate1 fact.proof) facts)
          catch _ => pure ()
          saved.restore
        return candidates
      else
        let arg ← mkFreshExprMVar (some domain)
        applyRuleCore (mkApp ruleProof arg) (body.instantiate1 arg) facts
  | _ =>
      let proposition ← instantiateMVars ruleType
      let proof ← instantiateMVars ruleProof
      if proposition.hasMVar || proof.hasMVar || !(← isProp proposition) then
        return #[]
      checkEvidence proposition proof
      return #[{ proposition, proof }]

private def applyRule (rule : Expr) (facts : Array KnownFact) : MetaM (Array Candidate) := do
  applyRuleCore rule (← inferType rule) facts

private def applyRulesOnce (config : Config) (state : BuildState) : MetaM (BuildState × Bool) := do
  let mut next := state
  let mut added := false
  for rule in config.rules do
    for candidate in ← applyRule rule state.knowledge.facts do
      if !factExists next.knowledge.facts candidate.proposition then
        let before := next.knowledge.facts.size
        next ← pushFact next config candidate.proposition candidate.proof
        added := added || next.knowledge.facts.size > before
  return (next, added)

private def saturate (config : Config) (initial : BuildState) : MetaM (BuildState × Bool) := do
  let mut state := initial
  let mut lastRoundAdded := false
  for _ in [0:config.maxRounds] do
    let (next, added) ← applyRulesOnce config state
    state := next
    lastRoundAdded := added
    if !added then
      return (state, state.hitFactLimit)
  return (state, state.hitFactLimit || lastRoundAdded)

private def proveCandidates (config : Config) (initial : BuildState) : MetaM BuildState := do
  let mut state := initial
  let candidateConfig := {
    config with engines := config.engines.filter (· != .simp)
  }
  for proposition in config.candidates do
    let proposition ← normalize proposition
    let proof? ← proveCandidate config proposition
    if let some proof := proof? then
      state ← decompose candidateConfig proof proposition state
  return state

private def contradiction? (state : BuildState) : MetaM (Option Expr) := do
  let facts := state.knowledge.facts
  for fact in facts do
    if (← normalize fact.proposition).isConstOf ``False then
      return some fact.proof
  for negative in facts do
    match ← whnf negative.proposition with
    | .forallE _ domain body _ =>
        if !body.hasLooseBVar 0 && (← normalize body).isConstOf ``False then
          for positive in facts do
            let saved ← saveState
            try
              if ← isDefEq domain positive.proposition then
                let proof ← instantiateMVars (mkApp negative.proof positive.proof)
                checkEvidence (.const ``False []) proof
                saved.restore
                return some proof
            catch _ => pure ()
            saved.restore
    | _ => pure ()
  return none

private def isTypeExpr (e : Expr) : MetaM Bool := do
  return (← whnf (← inferType e)).isSort

private partial def argumentAtoms (e : Expr) : MetaM (Array Expr) := do
  let mut atoms := #[]
  for arg in e.getAppArgs do
    unless ← isTypeExpr arg do
      if !atoms.any (· == arg) then
        atoms := atoms.push arg
      for nested in ← argumentAtoms arg do
        if !atoms.any (· == nested) then
          atoms := atoms.push nested
  return atoms

/-- Keep the connected component of facts containing `root`, preserving shared witness identity. -/
def projectToRoot (knowledge : RootedKnowledge) : MetaM RootedKnowledge := do
  let mut anchors := #[knowledge.root]
  let mut selected : Array KnownFact := #[]
  let mut changed := true
  while changed do
    changed := false
    for fact in knowledge.facts do
      if !selected.any (·.proposition == fact.proposition) &&
          anchors.any (containsExpr fact.proposition) then
        selected := selected.push fact
        changed := true
        for atom in ← argumentAtoms fact.proposition do
          if !anchors.any (· == atom) then
            anchors := anchors.push atom
  let kept := selected
  return knowledge.project
    (fun fact => kept.any (·.proposition == fact.proposition))
    (fun witness => kept.any fun fact => containsExpr fact.proposition witness.term)

/-- Extract finite, proof-backed knowledge about `root` without mutating the proof goal. -/
def extract (root : Expr) (config : Config := {}) : MetaM ExtractionResult := do
  let root ← normalize root
  let scope ← instantiateLCtxMVars (← getLCtx)
  let initial ← collectContext config { knowledge := .empty root scope }
  let (state, truncatedBeforeCandidates) ← saturate config initial
  let state ← proveCandidates config state
  let (state, truncatedAfterCandidates) ← saturate config state
  let automatedContradiction ← if config.uses .aesop then
    proveCandidate config (.const ``False [])
  else
    pure none
  let result ← if let some proof := automatedContradiction.or (← contradiction? state) then
    pure (ExtractionResult.inconsistent (← Inconsistency.ofProof root scope proof))
  else
    let knowledge := state.knowledge.withTruncated
      (truncatedBeforeCandidates || truncatedAfterCandidates)
    let knowledge ← if config.rootOnly then projectToRoot knowledge else pure knowledge
    pure (ExtractionResult.knowledge knowledge)
  if config.kernelCheck then
    result.kernelCertify
  return result

end Iykyk
