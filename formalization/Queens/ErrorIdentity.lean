import Queens.LocalBoard
import Queens.LowerColumns
import Queens.GoldenRatio
import Mathlib.Tactic.LinearCombination

/-!
# The one-step error identity

Section 6.6 proves Theorem 2 by a contraction that compares the counting error
`ε(x) = U(x) - x / φ` at column `n - 1` with the error at `m - 1`, where `m` is
the least unused row before column `n`. This file proves the identity behind it,
Lemma 21, for the actual greedy board. It is exact and holds before every
positive column; no finite verification enters.

## Main statements

* `Queens.upperCount_eq_reference_window`: `U(n - 1) = m + w - |D|`.
* `Queens.one_step_error_identity`: **Lemma 21 (one-step error identity)**,
  `ε(n - 1) = Y - ε(m - 1) / φ` with `Y = w - |D| + 1 - z / φ`.
-/

namespace Queens

open scoped goldenRatio

/-- The lower queens strictly before column `n` are counted by `L(n - 1)`.
This connects the local records with the global count in Lemma 21. -/
theorem earlierLowerColumns_card {n : ℕ} (hn : 0 < n) :
    (earlierLowerColumns n).card = lowerCount (n - 1) := by
  rw [← count_lower_eq_lowerCount, Nat.count_eq_card_filter_range]
  congr 1
  rw [Nat.sub_add_cancel hn]
  rfl

/-- The local diagonal rank identity gives `U(n - 1) = m + w - |D|`, the first
counting equation in the proof of Lemma 21. The lower queens in columns
`1, …, n - 1` use the `d - 1` magnitudes below `d` and the `|D|` recorded above
it. Signed arithmetic avoids truncated subtraction when the window is negative. -/
theorem upperCount_eq_reference_window {n : ℕ} (hn : 0 < n) :
    (upperCount (n - 1) : ℤ) = (rowReference n : ℤ) + window n -
      ((diagonalOffsets n).card : ℤ) := by
  have hrank := nextLowerRank_eq_reference_add_offsets n
  rw [nextLowerRank, earlierLowerColumns_card hn, lowerCount] at hrank
  have hbounded := upperCount_le (n - 1)
  unfold window
  omega

/-- The definition of `z` before column `n`: `n = m + U(m - 1) + z`. -/
theorem column_eq_reference_add_displacement (n : ℕ) :
    (n : ℤ) = (rowReference n : ℤ) + (countReference n : ℤ) + upperDisplacement n := by
  unfold upperDisplacement
  ring

/-- **Lemma 21 (one-step error identity).** Before every column `n ≥ 1`, with
least unused row `m` and records `w`, `z`, and `D`,
`ε(n - 1) = Y - ε(m - 1) / φ`, where `Y = w - |D| + 1 - z / φ`. -/
theorem one_step_error_identity {n : ℕ} (hn : 0 < n) :
    countError upperCount (n - 1) =
      ((window n : ℝ) - ((diagonalOffsets n).card : ℝ) + 1 - (upperDisplacement n : ℝ) / φ) -
        countError upperCount (rowReference n - 1) / φ := by
  have hcount : (upperCount (n - 1) : ℝ) =
      (rowReference n : ℝ) + (window n : ℝ) - ((diagonalOffsets n).card : ℝ) := by
    exact_mod_cast upperCount_eq_reference_window hn
  have hcolumn : (n : ℝ) = (rowReference n : ℝ) + (upperCount (rowReference n - 1) : ℝ) +
      (upperDisplacement n : ℝ) := by
    exact_mod_cast column_eq_reference_add_displacement n
  have hm : 1 ≤ rowReference n := rowReference_pos hn
  have hinv := inv_goldenRatio_sq
  rw [countError, countError, Nat.cast_sub hm, Nat.cast_sub hn, Nat.cast_one]
  linear_combination hcount - φ⁻¹ * hcolumn - ((rowReference n : ℝ) - 1) * hinv

end Queens
