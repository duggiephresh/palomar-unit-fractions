# Palomar submission: odd Znám solution and coprime Erdős #307 solution

- `Challenge.lean`: the two statements, with `sorry`. Theorem 1 copies formal-conjectures'
  `erdos_307.variants.coprime_one_notMem` field for field.
- `Solution.lean`: a self-contained proof (the library from github.com/duggiephresh/unit-fraction-solutions,
  concatenated). Axioms: `propext, Classical.choice, Quot.sound`. No `native_decide`, no `sorry`.
- `comparator.json`, `formalization.yaml`: Palomar registry metadata (formalization.yaml v0.4).

Build: `lake exe cache get && lake build` (Lean 4 v4.36.0, Mathlib v4.36.0).

Submission form: https://submit.palomar-registry.org/

**How this was produced.** The results, the search programs and this Lean formalization were produced by AI agents (Claude, Anthropic) in a project run by Doug Phillips. He set the goals, directed the work and is responsible for this entry, but he did not independently verify the mathematics. Palomar lists only humans as authors, following the Leiden Declaration; the AI's contribution is recorded in `formalization.yaml` (`automation`). Correctness of the stated theorems rests on Lean kernel checks, re-verified by Palomar. No human mathematician has yet reviewed the work, and expert review is welcome.
