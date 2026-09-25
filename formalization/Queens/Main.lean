import Queens.Counting
import Queens.LowerColumns
import Queens.LowerRows
import Queens.Permutation
import Queens.Sorting

/-!
# The main bounds, conditional on diagonal discrepancy

This file connects the actual greedy sequence to Sections 2 and 3 of the paper.
The explicit hypothesis is precisely the bounded diagonal discrepancy of Lemma 5.
`Queens.Exactness` proves that hypothesis and the unconditional main theorem.

`main_of_diagonalDiscrepancy` proves Theorem 1 from Lemma 5. The more general
`position_bounds_of_diagonalDiscrepancy` keeps the discrepancy constant `C`,
as in Proposition 8.
-/

namespace Queens

open scoped goldenRatio

/-- Magnitude of the lower diagonal at zero-based chronological rank `k`.
This is `dₖ₊₁` in Section 3, Lemma 5. -/
noncomputable def lowerDiagonal (k : ℕ) : ℕ :=
  lowerColumn k - q (lowerColumn k)

/-- The universal discrepancy hypothesis of Section 3, with the general
constant of Proposition 8. Lemma 5 asserts `DiagonalDiscrepancy 4`. -/
def DiagonalDiscrepancy (C : ℕ) : Prop :=
  ∀ k, |(lowerDiagonal k : ℤ) - ((k : ℤ) + 1)| ≤ (C : ℤ)

/-- Casting a lower-diagonal magnitude to the integers preserves subtraction
because the corresponding queen is below the main diagonal. -/
theorem lowerDiagonal_cast (k : ℕ) :
    (lowerDiagonal k : ℤ) = (lowerColumn k : ℤ) - (q (lowerColumn k) : ℤ) := by
  exact Nat.cast_sub (lowerColumn_lower (infinite_lowerColumns q_surjective) k).le

/-- The sorted rank of a chronological lower row. This supplies an explicit
rearrangement for the sorting step in Section 3, Lemma 6. -/
noncomputable def lowerRowRank (k : ℕ) : ℕ := by
  classical
  exact Nat.count IsLowerRow (q (lowerColumn k))

/-- Sorting a chronological lower row at its rank recovers that row. -/
theorem sortedLowerRow_lowerRowRank (k : ℕ) :
    sortedLowerRow (lowerRowRank k) = q (lowerColumn k) := by
  classical
  exact Nat.nth_count
    ⟨lowerColumn k, lowerColumn_lower (infinite_lowerColumns q_surjective) k, rfl⟩

/-- Chronological lower-row ranks give a permutation: both enumerations
contain exactly the lower rows, and neither repeats a row. -/
theorem lowerRowRank_bijective : Function.Bijective lowerRowRank := by
  constructor
  · intro i j hij
    apply (lowerColumn_strictMono (infinite_lowerColumns q_surjective)).injective
    apply q_injective
    rw [← sortedLowerRow_lowerRowRank i, ← sortedLowerRow_lowerRowRank j, hij]
  · intro n
    have hrow : IsLowerRow (sortedLowerRow n) :=
      (range_sortedLowerRow q_surjective).subset ⟨n, rfl⟩
    obtain ⟨col, hcol, hrow⟩ := hrow
    obtain ⟨k, hk⟩ := exists_lowerColumn_eq hcol
    refine ⟨k, (sortedLowerRow_strictMono q_surjective).injective ?_⟩
    rw [sortedLowerRow_lowerRowRank, hk, hrow]

/-- The permutation matching chronological lower rows with sorted lower
rows, used in Lemma 6. -/
noncomputable def lowerRowPermutation : Equiv.Perm ℕ :=
  Equiv.ofBijective lowerRowRank lowerRowRank_bijective

/-- The chronological-to-sorted permutation preserves each lower-row value. -/
theorem sortedLowerRow_lowerRowPermutation (k : ℕ) :
    sortedLowerRow (lowerRowPermutation k) = q (lowerColumn k) :=
  sortedLowerRow_lowerRowRank k

/-- The rank-row identity turns diagonal discrepancy into chronological
lower-row discrepancy, the first step of Section 3. -/
theorem chronological_row_discrepancy {C : ℕ} (hdiag : DiagonalDiscrepancy C)
    (k : ℕ) :
    |(q (lowerColumn k) : ℤ) - (upperCount (lowerColumn k) : ℤ)| ≤ (C : ℤ) := by
  apply lower_row_count_discrepancy (infinite_lowerColumns q_surjective) k
  simpa only [lowerDiagonal_cast] using hdiag k

/-- **Lemma 6, sorted-row bound.** Rearranging the chronological lower rows
preserves their discrepancy from `U(xᴸⱼ)`. -/
theorem sorted_row_discrepancy {C : ℕ} (hdiag : DiagonalDiscrepancy C) (k : ℕ) :
    |(sortedLowerRow k : ℤ) - (upperCount (lowerColumn k) : ℤ)| ≤ (C : ℤ) := by
  have hv : Monotone (fun i => (sortedLowerRow i : ℤ)) :=
    Nat.mono_cast.comp (sortedLowerRow_strictMono q_surjective).monotone
  have ht : Monotone (fun i => (upperCount (lowerColumn i) : ℤ)) :=
    Nat.mono_cast.comp (lowerColumn_upperCount_mono (infinite_lowerColumns q_surjective))
  apply abs_sub_le_of_monotone_rearrangement hv ht lowerRowPermutation
  intro i
  rw [sortedLowerRow_lowerRowPermutation]
  exact chronological_row_discrepancy hdiag i

/-- **Lemma 6, lower-column bound.** Combining the sorted-row estimate with
Lemma 4 gives the column estimate used in the counting recurrence. -/
theorem lower_column_discrepancy {C : ℕ} (hdiag : DiagonalDiscrepancy C) (k : ℕ) :
    |(lowerColumn k : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) - (upperCount k : ℤ)| ≤ (C : ℤ) := by
  have hsplit : (lowerColumn k : ℤ) = (upperCount (lowerColumn k) : ℤ) + (k : ℤ) + 1 := by
    exact_mod_cast lowerColumn_eq_upperCount_add_rank (infinite_lowerColumns q_surjective) k
  have heq : (lowerColumn k : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) - (upperCount k : ℤ) =
      -((sortedLowerRow k : ℤ) - (upperCount (lowerColumn k) : ℤ)) := by
    rw [sortedLowerRow_eq q_surjective, hsplit]
    push_cast
    ring
  rw [heq, abs_neg]
  exact sorted_row_discrepancy hdiag k

/-- **Lemma 7 for the greedy queens sequence.** The explicit input is the diagonal
discrepancy bound; all counting and endpoint facts are proved. -/
theorem countDefect_le_of_diagonalDiscrepancy {C : ℕ}
    (hdiag : DiagonalDiscrepancy C) (n : ℕ) :
    |countDefect upperCount n| ≤ (C : ℝ) + 1 := by
  apply counting_recurrence upperCount (fun j => lowerColumn (j - 1)) C
    upperCount_zero upperCount_le
  · intro m
    rw [upperCount_succ]
    split_ifs <;> omega
  · intro m hm
    exact lowerColumn_left m hm
  · intro m
    simpa only [Nat.add_sub_cancel, lowerCount] using
      lowerColumn_right (infinite_lowerColumns q_surjective) m
  · intro j hj
    simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using
      lower_column_discrepancy hdiag (j - 1)

/-- **Proposition 8, count estimate.** Diagonal discrepancy controls the
distance of the actual greedy upper count from the golden-ratio slope. -/
theorem upperCount_error_of_diagonalDiscrepancy {C : ℕ}
    (hdiag : DiagonalDiscrepancy C) (n : ℕ) :
    |countError upperCount n| < φ⁻¹ * ((C : ℝ) + 1) :=
  count_error_lt upperCount C upperCount_zero upperCount_le
    (fun _ hn => upperCount_pos hn) (countDefect_le_of_diagonalDiscrepancy hdiag) n

/-- **Proposition 8, queen positions.** For the actual greedy construction,
the two golden-ratio bounds follow from the universal discrepancy bound. -/
theorem position_bounds_of_diagonalDiscrepancy {C : ℕ}
    (hdiag : DiagonalDiscrepancy C) (n : ℕ) :
    (n < q n → |(q n : ℝ) - (n : ℝ) * φ| < ((C : ℝ) + 1) / φ) ∧
    (q n < n → |(q n : ℝ) - (n : ℝ) / φ| < (C : ℝ) + ((C : ℝ) + 1) / φ) := by
  have hcount := upperCount_error_of_diagonalDiscrepancy hdiag n
  constructor
  · intro hn
    simpa only [div_eq_mul_inv, mul_comm] using
      upper_position_error_lt upperCount (q n) n _ (q_eq_add_upperCount hn) hcount
  · intro hn
    have hlower : |(q n : ℝ) - (upperCount n : ℝ)| ≤ (C : ℝ) := by
      obtain ⟨k, rfl⟩ := exists_lowerColumn_eq hn
      exact_mod_cast chronological_row_discrepancy hdiag k
    simpa only [div_eq_mul_inv, mul_comm] using
      lower_position_error_lt upperCount (q n) n (C : ℝ) _ hlower hcount

/-- **Theorem 1 from Lemma 5.** This separates the pure mathematical deduction
from the finite verification. `Queens.main` in `Exactness` supplies the proved
diagonal discrepancy and removes the hypothesis. -/
theorem main_of_diagonalDiscrepancy (hdiag : DiagonalDiscrepancy 4) (n : ℕ) :
    (n < q n → |(q n : ℝ) - (n : ℝ) * φ| < 5 / φ) ∧
    (q n < n → |(q n : ℝ) - (n : ℝ) / φ| < 4 + 5 / φ) := by
  simpa only [Nat.cast_ofNat, show (4 : ℝ) + 1 = 5 by norm_num] using
    position_bounds_of_diagonalDiscrepancy hdiag n

end Queens
