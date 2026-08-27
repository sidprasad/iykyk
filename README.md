# Lean Knowledge

Lean Knowledge is a proposed library for extracting what a Lean proof context
establishes about a selected value. The result is ordinary, proof-backed data
that can be inspected or passed to other tools.

The project is currently a design repository. See
[DESIGN.md](./DESIGN.md) for the motivation, semantic contract, proposed
boundary, and initial examples.

Spytial is one intended consumer: it can translate extracted knowledge into a
relational data instance and visualize that instance. Visualization is not part
of this library's core contract.
