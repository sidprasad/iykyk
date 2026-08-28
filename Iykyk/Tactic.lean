module

public import Iykyk.Query
public meta import Iykyk.Query

public section

/-!
# Interactive extraction

`iykyk term` reports proof-backed knowledge without changing the goal. Clauses select explicit or
local forward rules, established-fact saturation, named candidate propositions, and proof engines.

Academic lineage: typed-hole and live-programming systems motivate exposing useful semantics while
work is incomplete, without making the proof-state display itself the public result. See
`README.md`.
-/

namespace Iykyk

open Lean Meta Elab Tactic

private meta def elaborateRule (stx : Syntax) : TacticM Expr := do
  instantiateMVars (← Term.elabTerm stx none)

private meta def elaborateSimpOnlyRule (stx : Syntax) : TacticM Expr := do
  if stx.isIdent then
    if let some rule ← Term.resolveId? stx (withInfo := true) then
      return rule
  elaborateRule stx

private meta def elaborateCandidate (stx : Syntax) : TacticM Expr := do
  let proposition ← instantiateMVars (← Term.elabTerm stx (some (.sort .zero)))
  unless ← isProp proposition do
    throwErrorAt stx "iykyk candidate must be a proposition"
  return proposition

private structure ParsedClauses where
  rules : Array Syntax := #[]
  useLocalRules : Bool := false
  useEstablishedRules : Bool := false
  candidates : Array Syntax := #[]
  engines : Array ProofEngine := #[]
  simpOnlyRules : Option (Array Syntax) := none

private inductive ParsedEngine where
  | simp
  | simpOnly (rules : Array Syntax)
  | aesop

declare_syntax_cat iykykEngine
syntax "simp" : iykykEngine
syntax "simp" "only" "[" term,* "]" : iykykEngine
syntax "aesop" : iykykEngine

declare_syntax_cat iykykClause
syntax "using " "[" term,* "]" : iykykClause
syntax "using " "*" : iykykClause
syntax "using " "facts" : iykykClause
syntax "deriving " "[" term,* "]" : iykykClause
syntax "with " "[" iykykEngine,* "]" : iykykClause

private meta def parseEngine (stx : Syntax) : TacticM ParsedEngine := do
  match stx with
  | `(iykykEngine| simp) => return .simp
  | `(iykykEngine| simp only [$rules:term,*]) => return .simpOnly rules.getElems
  | `(iykykEngine| aesop) => return .aesop
  | _ => throwErrorAt stx "unknown iykyk proof engine"

private meta def parseClauses (clauses : Array Syntax) : TacticM ParsedClauses := do
  let mut parsed : ParsedClauses := {}
  for clause in clauses do
    match clause with
    | `(iykykClause| using [$rules:term,*]) =>
        parsed := { parsed with rules := parsed.rules ++ rules.getElems }
    | `(iykykClause| using *) =>
        parsed := { parsed with useLocalRules := true }
    | `(iykykClause| using facts) =>
        parsed := { parsed with useEstablishedRules := true }
    | `(iykykClause| deriving [$candidates:term,*]) =>
        parsed := { parsed with candidates := parsed.candidates ++ candidates.getElems }
    | `(iykykClause| with [$engines:iykykEngine,*]) =>
        for engineStx in engines.getElems do
          match ← parseEngine engineStx with
          | .simp =>
              if parsed.simpOnlyRules.isSome then
                throwErrorAt engineStx "iykyk: cannot combine `simp` and `simp only`"
              if !parsed.engines.contains .simp then
                parsed := { parsed with engines := parsed.engines.push .simp }
          | .simpOnly rules =>
              if parsed.engines.contains .simp then
                throwErrorAt engineStx "iykyk: cannot combine `simp` and `simp only`"
              parsed := { parsed with
                engines := parsed.engines.push .simp
                simpOnlyRules := some rules }
          | .aesop =>
              if !parsed.engines.contains .aesop then
                parsed := { parsed with engines := parsed.engines.push .aesop }
    | _ => throwErrorAt clause "invalid iykyk clause"
  return parsed

private meta def engineName (config : Config) : ProofEngine → String
  | .simp => if config.simpOnlyRules.isSome then "simp only" else "simp"
  | .aesop => "aesop"

private meta def hookNames (config : Config) : Array String := Id.run do
  let mut names := #[]
  if config.useLocalRules then
    names := names.push "local rules"
  if config.useEstablishedRules then
    names := names.push "established rules"
  for engine in config.engines do
    names := names.push (engineName config engine)
  return names

private meta def renderKnowledge (result : ExtractionResult) (config : Config) :
    MetaM String := do
  let hooks := hookNames config
  match result with
  | .inconsistent inconsistency =>
      let automation := if hooks.isEmpty then "" else
        s!"\n  under the hood: {String.intercalate ", " hooks.toList}"
      return s!"iykyk\n  root: {← ppExpr inconsistency.root}{automation}\n  status: inconsistent"
  | .knowledge knowledge =>
      let mut lines := #["iykyk", s!"  root: {← ppExpr knowledge.root}"]
      if !hooks.isEmpty then
        lines := lines.push s!"  under the hood: {String.intercalate ", " hooks.toList}"
      if knowledge.witnesses.isEmpty then
        lines := lines.push "  witnesses: (none)"
      else
        lines := lines.push "  witnesses:"
        for witness in knowledge.witnesses do
          let type ← ppExpr witness.type
          let term ← ppExpr witness.term
          lines := lines.push s!"    •{witness.id} : {type} := {term}"
      if knowledge.facts.isEmpty then
        lines := lines.push "  facts: (none)"
      else
        lines := lines.push "  facts:"
        for index in [:knowledge.facts.size] do
          lines := lines.push s!"    [{index}] {← ppExpr knowledge.facts[index]!.proposition}"
      lines := lines.push s!"  certificate: {← ppExpr (← knowledge.certificate).proposition}"
      lines := lines.push s!"  status: {if knowledge.truncated then "truncated" else "complete"}"
      return String.intercalate "\n" lines.toList

private meta def runIykyk (rootStx : Syntax) (clauseStxs : Array Syntax) : TacticM Unit :=
  withMainContext do
    let clauses ← parseClauses clauseStxs
    let root ← instantiateMVars (← Term.elabTerm rootStx none)
    let rules ← clauses.rules.mapM elaborateRule
    let candidates ← clauses.candidates.mapM elaborateCandidate
    let simpOnlyRules ← match clauses.simpOnlyRules with
      | none => pure none
      | some rules => pure (some (← rules.mapM elaborateSimpOnlyRule))
    let config : Config := {
      rules
      useLocalRules := clauses.useLocalRules
      useEstablishedRules := clauses.useEstablishedRules
      candidates
      engines := clauses.engines
      simpOnlyRules
    }
    logInfo (← renderKnowledge (← extract root config) config)

syntax (name := iykyk) "iykyk " term iykykClause* : tactic

elab_rules : tactic
  | `(tactic| iykyk $root:term $clauses:iykykClause*) => runIykyk root clauses

end Iykyk
