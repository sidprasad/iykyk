# Metatheory boundary

`IykykMetatheory.lean` formalizes the stable semantic contract without modeling Lean internals:

- contexts are predicates selecting possible worlds;
- facts are predicates that must hold in every selected world;
- every supported derivation is sound;
- projection and truncation preserve soundness;
- context strengthening preserves known facts;
- existential decomposition retains one shared witness;
- only consequences common to both disjunctive branches may be exposed; and
- inconsistency is equivalent to having no compatible world.

The operational extractor works with `Lean.Expr`, `LocalContext`, and `MetaM`. Its small trusted
bridge is the check in `Iykyk/Extract.lean` that infers each proof expression's type and compares it
with the reported proposition. Formalizing Lean's expression evaluator or kernel is intentionally
outside this project. Thus `extract_sound` proves the semantic calculus, while the bridge is
responsible for ensuring that each runtime `KnownFact` represents a `Derivation.certificate`.
