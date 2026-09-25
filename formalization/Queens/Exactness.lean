import Queens.GeneralExactness
import Queens.Identification

/-!
# The local calculation follows the actual board

This file assembles Lemma 16 from the separately proved request, candidate,
source-test, row-search, and update semantics. Proposition 17 supplies successful
termination of every branch. The actual branch is retained at each traversal,
and therefore one certified successor represents the next actual board.
-/

namespace Queens

/-- **Lemma 16 (the records determine the actual step)**, in the exact form
needed by the induction of Section 6.4. The preliminary extension, candidate
choice, and finishing traversal each retain the actual branch. -/
theorem local_step_exact : LocalStepExact := by
  intro n hn s next hrep hc hword hcalculate
  apply local_step_exact_of_memory (by decide)
    (show Finite.historyLength < rowReference n from
      lt_of_lt_of_le (by decide) (rowReference_ge_nineteen hn))
    (countReference_ge_twelve hn) Finite.historyGraph_wellFormed hrep hc hword hcalculate

/-- **Lemma 5 (bounded diagonal discrepancy).** The chronological lower
diagonal of positive rank `k + 1` differs from that rank by at most four. -/
theorem bounded_diagonal_discrepancy : DiagonalDiscrepancy 4 :=
  diagonalDiscrepancy_of_localStepExact local_step_exact

/-- **Theorem 1.** The actual greedy queens lie within the paper's stated
strict bounds of the two golden-ratio lines. The statement also covers `n = 0`,
where both implications have false antecedents. -/
theorem main (n : ℕ) :
    (n < q n → |(q n : ℝ) - (n : ℝ) * Real.goldenRatio| < 5 / Real.goldenRatio) ∧
    (q n < n → |(q n : ℝ) - (n : ℝ) / Real.goldenRatio| < 4 + 5 / Real.goldenRatio) :=
  main_of_diagonalDiscrepancy bounded_diagonal_discrepancy n

end Queens
