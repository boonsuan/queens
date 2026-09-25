# Formalization standards

The user requests readable Lean + mathlib code of a quality suitable for review
by mathlib contributors. Follow the supplied kit's mathematical priorities.

- Define the greedy sequence from its least-unattacked-row rule.
- Keep mathematical lemmas separate from finite data and computation.
- Give public definitions and theorems meaningful docstrings identifying their
  purpose and the corresponding paper section, definition, or result.
- Prefer reusable statements, explicit hypotheses, and small named intermediate
  results to large opaque tactic scripts.
- Preserve the manuscript and reference code in `queens-formalization-kit/`.
- Do not introduce `sorry`, project axioms, or assumptions disguised as proved
  paper results. A conditional theorem must be named and documented as conditional.
- Keep generated certificate data reproducible; no Python assertion is a Lean proof.
- All final proofs must be checked by the Lean kernel. Do not use `native_decide`,
  native reduction axioms, or other compiler-trusting shortcuts. Use `decide`,
  `decide +kernel`, ordinary proof terms, or proved certificate checkers whose
  concrete checks also reduce in the kernel. This is the user's explicit
  requirement and supersedes the kit's permission to use native evaluation.
- Maintain `AxiomAudit.lean` and verify that the final paper results depend only
  on the usual foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Run `lake build` after integration and report the precise remaining obligations.
- Follow the paper as written; report a mathematical discrepancy rather than silently
  weakening or changing its statements.
