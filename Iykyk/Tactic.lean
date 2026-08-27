module

public import Iykyk.Query
public meta import Iykyk.Query

public section

/-!
# Interactive extraction

`iykyk term` reports proof-backed knowledge without changing the goal. Clauses add caller-supplied
forward rules, named candidate propositions, and explicitly selected proof engines.

Academic lineage: typed-hole and live-programming systems motivate exposing useful semantics while
work is incomplete, without making the proof-state display itself the public result. See
`README.md`.
-/

namespace Iykyk

open Lean Meta Elab Tactic

private meta def elaborateRule (stx : Syntax) : TacticM Expr := do
  instantiateMVars (← Term.elabTerm stx none)

private meta def elaborateCandidate (stx : Syntax) : TacticM Expr := do
  let proposition ← instantiateMVars (← Term.elabTerm stx (some (.sort .zero)))
  unless ← isProp proposition do
    throwErrorAt stx "iykyk candidate must be a proposition"
  return proposition

private structure ParsedClauses where
  rules : Array Syntax := #[]
  candidates : Array Syntax := #[]
  engines : Array ProofEngine := #[]

declare_syntax_cat iykykEngine
syntax "simp" : iykykEngine
syntax "aesop" : iykykEngine

declare_syntax_cat iykykClause
syntax "using " "[" term,* "]" : iykykClause
syntax "deriving " "[" term,* "]" : iykykClause
syntax "with " "[" iykykEngine,* "]" : iykykClause

private meta def parseEngine (stx : Syntax) : TacticM ProofEngine := do
  match stx with
  | `(iykykEngine| simp) => return .simp
  | `(iykykEngine| aesop) => return .aesop
  | _ => throwErrorAt stx "unknown iykyk proof engine"

private meta def parseClauses (clauses : Array Syntax) : TacticM ParsedClauses := do
  let mut parsed : ParsedClauses := {}
  for clause in clauses do
    match clause with
    | `(iykykClause| using [$rules:term,*]) =>
        parsed := { parsed with rules := parsed.rules ++ rules.getElems }
    | `(iykykClause| deriving [$candidates:term,*]) =>
        parsed := { parsed with candidates := parsed.candidates ++ candidates.getElems }
    | `(iykykClause| with [$engines:iykykEngine,*]) =>
        for engineStx in engines.getElems do
          let engine ← parseEngine engineStx
          if !parsed.engines.contains engine then
            parsed := { parsed with engines := parsed.engines.push engine }
    | _ => throwErrorAt clause "invalid iykyk clause"
  return parsed

private meta def engineName : ProofEngine → String
  | .simp => "simp"
  | .aesop => "aesop"

private meta def renderKnowledge (result : ExtractionResult) (engines : Array ProofEngine) :
    MetaM String := do
  match result with
  | .inconsistent inconsistency =>
      let automation := if engines.isEmpty then "" else
        s!"\n  under the hood: {String.intercalate ", " (engines.map engineName).toList}"
      return s!"iykyk\n  root: {← ppExpr inconsistency.root}{automation}\n  status: inconsistent"
  | .knowledge knowledge =>
      let mut lines := #["iykyk", s!"  root: {← ppExpr knowledge.root}"]
      if !engines.isEmpty then
        lines := lines.push s!"  under the hood: {
          String.intercalate ", " (engines.map engineName).toList}"
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
    let config : Config := { rules, candidates, engines := clauses.engines }
    logInfo (← renderKnowledge (← extract root config) clauses.engines)

syntax (name := iykyk) "iykyk " term iykykClause* : tactic

elab_rules : tactic
  | `(tactic| iykyk $root:term $clauses:iykykClause*) => runIykyk root clauses

end Iykyk
