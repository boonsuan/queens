import Queens.ErrorRecursion
import Queens.SharpAnalysis
import Queens.SharpRecords

/-!
# Sharper golden-ratio bounds

This file proves Proposition 21 in Section 6.6 for the actual greedy sequence.
The count estimate combines Lemma 20's exact recursion with the additional
finite record checks. The position bounds then use the change in the count
at an upper or lower column, and the asymmetric lower-diagonal estimate.
-/

namespace Queens

open scoped goldenRatio

/-- **Proposition 21, upper-count error.** The actual upper count lies
strictly between `n / φ - 3 / φ` and `n / φ + 2 / φ`, including at the origin. -/
theorem sharp_count_error (n : ℕ) :
    -3 / φ < countError upperCount n ∧ countError upperCount n < 2 / φ := by
  apply sharp_error_bounds_of_recursion (countError upperCount)
    (fun _ hn => Finite.prefix_sharp_count_error hn) ?_ n
  intro k hk
  refine ⟨referenceLowerRank (k + 1), ?_,
    (window (k + 1) : ℝ) - ((diagonalOffsets (k + 1)).card : ℝ) -
      φ * ((rowOffsets (k + 1)).card : ℝ), ?_⟩
  · simpa using referenceLowerRank_lt (show 2 ≤ k + 1 by omega)
  · obtain ⟨hl, hu⟩ := sharp_record_bounds (k + 1) (by omega)
    exact ⟨hl, hu, by simpa using exact_error_recursion (show 0 < k + 1 by omega)⟩

/-- Section 6.6: at an upper column the position error is exactly the
upper-count error, using Lemma 2's upper-row formula. -/
theorem upper_position_error_eq_countError {n : ℕ} (hn : n < q n) :
    (q n : ℝ) - (n : ℝ) * φ = countError upperCount n :=
  upper_position_error_eq upperCount (q n) n (q_eq_add_upperCount hn)

/-- Section 6.6: the error increment distinguishes upper and lower columns.
The origin is excluded because it is neither an upper nor a lower queen. -/
theorem countError_succ (n : ℕ) :
    countError upperCount (n + 1) = countError upperCount n +
      (if n + 1 < q (n + 1) then 1 else 0) - φ⁻¹ := by
  rw [countError, countError, upperCount_succ, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  split_ifs <;> norm_num <;> ring

/-- **Proposition 21, upper queens.** Using the upper-column increment
sharpens the lower endpoint beyond the uniform count estimate. -/
theorem sharp_upper_position {n : ℕ} (hn : n < q n) :
    1 - 4 / φ < (q n : ℝ) - (n : ℝ) * φ ∧
      (q n : ℝ) - (n : ℝ) * φ < 2 / φ := by
  rw [upper_position_error_eq_countError hn]
  refine ⟨?_, (sharp_count_error n).2⟩
  cases n with
  | zero => simp at hn
  | succ n =>
    have hstep := countError_succ n
    rw [if_pos hn] at hstep
    have hl := (sharp_count_error n).1
    simp only [div_eq_mul_inv] at hl hstep ⊢
    linarith

/-- Section 6.6: at every lower queen the error of the row relative to the
upper count is between `-2` and `4`, by the two diagonal-discrepancy bounds. -/
theorem sharp_lower_row_count {n : ℕ} (hn : q n < n) :
    -2 ≤ (q n : ℝ) - (upperCount n : ℝ) ∧
      (q n : ℝ) - (upperCount n : ℝ) ≤ 4 := by
  obtain ⟨k, rfl⟩ := exists_lowerColumn_eq hn
  have hid := lower_row_count_identity (infinite_lowerColumns q_surjective) k
  have hsharp := lower_diagonal_discrepancy_le_two k
  rw [lowerDiagonal_cast] at hsharp
  have hfull := chronological_row_discrepancy bounded_diagonal_discrepancy k
  rw [abs_le] at hfull
  have hl : (-2 : ℤ) ≤ (q (lowerColumn k) : ℤ) - (upperCount (lowerColumn k) : ℤ) := by
    omega
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hfull.2⟩

/-- **Proposition 21, lower queens.** The lower-column increment and the
asymmetric diagonal estimates give the sharper two-sided row bounds. -/
theorem sharp_lower_position {n : ℕ} (hn : q n < n) :
    -2 - 4 / φ < (q n : ℝ) - (n : ℝ) / φ ∧
      (q n : ℝ) - (n : ℝ) / φ < 4 + 1 / φ := by
  obtain ⟨hlrow, hurow⟩ := sharp_lower_row_count hn
  cases n with
  | zero => omega
  | succ n =>
    have hstep := countError_succ n
    rw [if_neg (by omega)] at hstep
    obtain ⟨hl, hu⟩ := sharp_count_error n
    rw [lower_position_error_eq upperCount (q (n + 1)) (n + 1)]
    simp only [div_eq_mul_inv, one_mul] at hl hu hstep ⊢
    constructor <;> linarith

/-- **Proposition 21 (sharper constants).** Both branches of the greedy
queen permutation satisfy the paper's strict asymmetric golden-ratio bounds.
The two implications also hold vacuously at the origin. -/
theorem sharper_bounds (n : ℕ) :
    (n < q n → 1 - 4 / φ < (q n : ℝ) - (n : ℝ) * φ ∧
      (q n : ℝ) - (n : ℝ) * φ < 2 / φ) ∧
    (q n < n → -2 - 4 / φ < (q n : ℝ) - (n : ℝ) / φ ∧
      (q n : ℝ) - (n : ℝ) / φ < 4 + 1 / φ) :=
  ⟨sharp_upper_position, sharp_lower_position⟩

end Queens
