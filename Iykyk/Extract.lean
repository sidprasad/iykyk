module

public import Iykyk.Automation

public section

/-!
# Certified extraction engine

This deliberately small engine decomposes conjunctions and existentials, applies explicit
Horn-style rules, asks opt-in engines about named candidates, detects contradictions, and optionally
keeps only facts connected to the selected root. Every inserted fact is checked against its proof.

Academic lineage: the database chase motivates explicit forward rounds; abstract interpretation and
shape analysis motivate a sound finite result with a separate `truncated` bit. See `README.md`.
-/

namespace Iykyk

open Lean Meta

private structure BuildState where
  witnesses : Array Witness := #[]
  facts : Array KnownFact := #[]
  hitFactLimit : Bool := false

private structure Candidate where
  proposition : Expr
  proof : Expr

private def normalize (e : Expr) : MetaM Expr := do
  whnf (← instantiateMVars e)

private def validateFact (proposition proof : Expr) : MetaM Unit := do
  let proofType ← normalize (← inferType proof)
  let proposition ← normalize proposition
  unless ← isDefEq proofType proposition do
    throwError "iykyk internal error: proof does not establish extracted fact\n\
      proof type: {proofType}\n  fact: {proposition}"

private def containsExpr (haystack needle : Expr) : Bool :=
  haystack == needle || (haystack.find? (· == needle)).isSome

private def factExists (facts : Array KnownFact) (proposition : Expr) : Bool :=
  facts.any fun fact => fact.proposition == proposition

private def pushFact (state : BuildState) (config : Config) (proposition proof : Expr) :
    MetaM BuildState := do
  let proposition ← normalize proposition
  let proof ← instantiateMVars proof
  if factExists state.facts proposition then
    return state
  if state.facts.size >= config.maxFacts then
    return { state with hitFactLimit := true }
  validateFact proposition proof
  return { state with facts := state.facts.push { proposition, proof } }

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
  else if proposition.isAppOfArity ``Exists 2 then
    let args := proposition.getAppArgs
    let witnessId := state.witnesses.size
    let witness : Witness := {
      id := witnessId
      type := args[0]!
      term := ← mkAppM ``Classical.choose #[proof]
    }
    let specProof ← mkAppM ``Classical.choose_spec #[proof]
    let state := { state with witnesses := state.witnesses.push witness }
    decompose config specProof (← inferType specProof) state
  else
    pushFact state config proposition proof

private def collectContext (config : Config) : MetaM BuildState := do
  let mut state : BuildState := {}
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
      validateFact proposition proof
      return #[{ proposition, proof }]

private def applyRule (rule : Expr) (facts : Array KnownFact) : MetaM (Array Candidate) := do
  applyRuleCore rule (← inferType rule) facts

private def applyRulesOnce (config : Config) (state : BuildState) : MetaM (BuildState × Bool) := do
  let mut next := state
  let mut added := false
  for rule in config.rules do
    for candidate in ← applyRule rule state.facts do
      if !factExists next.facts candidate.proposition then
        let before := next.facts.size
        next ← pushFact next config candidate.proposition candidate.proof
        added := added || next.facts.size > before
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
  for fact in state.facts do
    if (← normalize fact.proposition).isConstOf ``False then
      return some fact.proof
  for negative in state.facts do
    match ← whnf negative.proposition with
    | .forallE _ domain body _ =>
        if !body.hasLooseBVar 0 && (← normalize body).isConstOf ``False then
          for positive in state.facts do
            let saved ← saveState
            try
              if ← isDefEq domain positive.proposition then
                let proof ← instantiateMVars (mkApp negative.proof positive.proof)
                validateFact (.const ``False []) proof
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
  let witnesses := knowledge.witnesses.filter fun witness =>
    selected.any fun fact => containsExpr fact.proposition witness.term
  return { knowledge with witnesses, facts := selected }

/-- Extract finite, proof-backed knowledge about `root` without mutating the proof goal. -/
def extract (root : Expr) (config : Config := {}) : MetaM ExtractionResult := do
  let root ← normalize root
  let scope ← getLCtx
  let initial ← collectContext config
  let (state, truncatedBeforeCandidates) ← saturate config initial
  let state ← proveCandidates config state
  let (state, truncatedAfterCandidates) ← saturate config state
  let automatedContradiction ← if config.uses .aesop then
    proveCandidate config (.const ``False [])
  else
    pure none
  if let some proof := automatedContradiction.or (← contradiction? state) then
    validateFact (.const ``False []) proof
    return .inconsistent root scope proof
  let knowledge : RootedKnowledge := {
    root
    scope
    witnesses := state.witnesses
    facts := state.facts
    truncated := truncatedBeforeCandidates || truncatedAfterCandidates
  }
  let knowledge ← if config.rootOnly then projectToRoot knowledge else pure knowledge
  return .knowledge knowledge

end Iykyk
