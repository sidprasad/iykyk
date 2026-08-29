module

public import Iykyk.Query
public meta import Iykyk.Query

public section

/-!
# Interactive extraction

`wdyk term` reports an `Afaik` without changing the goal. `fyi` selects explicit or established
forward rules, while `via` selects proof-producing normalization.

Academic lineage: typed-hole and live-programming systems motivate exposing useful semantics while
work is incomplete, without making the proof-state display itself the public result. See
`README.md`.
-/

namespace Iykyk

open Lean Meta Elab Tactic

private meta def elaborateFyi (stx : Syntax) : TacticM Expr := do
  let proof ← instantiateMVars (← Term.elabTerm stx none)
  unless ← isProp (← inferType proof) do
    throwErrorAt stx "`fyi` expects a proof of a proposition"
  return proof

private meta def elaborateSimpOnlyRule (stx : Syntax) : TacticM Expr := do
  if stx.isIdent then
    if let some rule ← Term.resolveId? stx (withInfo := true) then
      return rule
  elaborateFyi stx

private structure ParsedClauses where
  fyiTerms : Array Syntax := #[]
  useEstablishedRules : Bool := false
  mechanisms : Array Via := #[]
  simpOnlyRules : Option (Array Syntax) := none

private inductive ParsedVia where
  | simp
  | simpOnly (rules : Array Syntax)

declare_syntax_cat wdykVia
syntax "simp" : wdykVia
syntax "simp" "only" "[" term,* "]" : wdykVia

declare_syntax_cat wdykClause
syntax "fyi " "[" term,* "]" : wdykClause
syntax "fyi " "*" : wdykClause
syntax "via " "[" wdykVia,* "]" : wdykClause

private meta def parseVia (stx : Syntax) : TacticM ParsedVia := do
  match stx with
  | `(wdykVia| simp) => return .simp
  | `(wdykVia| simp only [$rules:term,*]) => return .simpOnly rules.getElems
  | _ => throwErrorAt stx "unknown `via` mechanism"

private meta def parseClauses (clauses : Array Syntax) : TacticM ParsedClauses := do
  let mut parsed : ParsedClauses := {}
  for clause in clauses do
    match clause with
    | `(wdykClause| fyi [$hypotheses:term,*]) =>
        parsed := { parsed with fyiTerms := parsed.fyiTerms ++ hypotheses.getElems }
    | `(wdykClause| fyi *) =>
        parsed := { parsed with useEstablishedRules := true }
    | `(wdykClause| via [$mechanisms:wdykVia,*]) =>
        for mechanismStx in mechanisms.getElems do
          match ← parseVia mechanismStx with
          | .simp =>
              if parsed.simpOnlyRules.isSome then
                throwErrorAt mechanismStx "wdyk: cannot combine `simp` and `simp only`"
              if !parsed.mechanisms.contains .simp then
                parsed := { parsed with mechanisms := parsed.mechanisms.push .simp }
          | .simpOnly rules =>
              if parsed.mechanisms.contains .simp then
                throwErrorAt mechanismStx "wdyk: cannot combine `simp` and `simp only`"
              parsed := { parsed with
                mechanisms := parsed.mechanisms.push .simp
                simpOnlyRules := some rules }
    | _ => throwErrorAt clause "invalid wdyk clause"
  return parsed

private meta def mechanismName (config : Config) : Via → String
  | .simp => if config.simpOnlyRules.isSome then "simp only" else "simp"

private meta def hookNames (config : Config) : Array String := Id.run do
  let mut names := #[]
  if config.useEstablishedRules then
    names := names.push "established rules"
  for mechanism in config.mechanisms do
    names := names.push (mechanismName config mechanism)
  return names

private meta def renderAfaik (result : WdykResult) (config : Config) : MetaM String := do
  let hooks := hookNames config
  match result with
  | .inconsistent inconsistency =>
      let automation := if hooks.isEmpty then "" else
        s!"\n  under the hood: {String.intercalate ", " hooks.toList}"
      return s!"afaik\n  root: {← ppExpr inconsistency.root}{automation}\n  status: inconsistent"
  | .afaik knowledge =>
      let mut lines := #["afaik", s!"  root: {← ppExpr knowledge.root}"]
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
      lines := lines.push s!"  status: {if knowledge.truncated then "truncated" else "saturated"}"
      return String.intercalate "\n" lines.toList

private meta def runWdyk (rootStx : Syntax) (clauseStxs : Array Syntax) : TacticM Unit :=
  withMainContext do
    let clauses ← parseClauses clauseStxs
    let root ← instantiateMVars (← Term.elabTerm rootStx none)
    let fyiTerms ← clauses.fyiTerms.mapM elaborateFyi
    let simpOnlyRules ← match clauses.simpOnlyRules with
      | none => pure none
      | some rules => pure (some (← rules.mapM elaborateSimpOnlyRule))
    let config : Config := {
      hypotheses := fyiTerms
      useEstablishedRules := clauses.useEstablishedRules
      mechanisms := clauses.mechanisms
      simpOnlyRules
    }
    logInfo (← renderAfaik (← wdyk root config) config)

syntax (name := wdykTactic) "wdyk " term wdykClause* : tactic

elab_rules : tactic
  | `(tactic| wdyk $root:term $clauses:wdykClause*) => runWdyk root clauses

end Iykyk
