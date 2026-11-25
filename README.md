# Palomar package: odd Znám solution and coprime Erdős #307 solution

- `Challenge.lean`: the two statements, with `sorry`. Theorem 1 copies formal-conjectures'
  `erdos_307.variants.coprime_one_notMem` field for field.
- `Solution.lean`: a self-contained proof. It is the library from
  github.com/duggiephresh/unit-fraction-solutions, concatenated. Axioms: `propext, Classical.choice, Quot.sound`.
  No `native_decide`, no `sorry`.
- `comparator.json`, `formalization.yaml`: Palomar registry metadata.

Build: `lake exe cache get && lake build` (Lean 4 v4.36.0, Mathlib v4.36.0).

Written with AI agents (Claude, Anthropic) under human direction; see `formalization.yaml`.
