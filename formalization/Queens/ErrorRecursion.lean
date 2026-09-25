import Queens.LocalBoard
import Queens.LowerColumns
import Queens.LowerRows
import Queens.Permutation
import Queens.GoldenRatio

/-!
# The exact upper-count error recursion

Section 6, Lemma 20 expresses the global counting error in terms of the local
records and an error at a smaller argument. The argument is the number of lower
rows strictly below the least unused row. The counting identities in this file
hold before every positive column; only the strict decrease needs column two.
No finite-state certificate is needed for this exact identity.
-/

namespace Queens

open scoped goldenRatio

/-- A finite set's least unused natural number is at most its cardinality.
This counting fact bounds the row reference in the proof of Lemma 20. -/
theorem leastUnused_le_card (s : Finset ℕ) : leastUnused s ≤ s.card := by
  have hsubset : Finset.range (leastUnused s) ⊆ s := by
    intro r hr
    exact mem_of_lt_leastUnused (Finset.mem_range.mp hr)
  simpa using Finset.card_le_card hsubset

/-- There is an unused row among `0, …, n` before column `n`.
This is the reference bound used in Section 6, Lemma 20. -/
theorem rowReference_le (n : ℕ) : rowReference n ≤ n := by
  have h := leastUnused_le_card (occupiedRows n)
  simpa [rowReference, occupiedRows, Finset.card_image_of_injective _ q_injective] using h

/-- The least unused row after the origin is a lower row: an upper queen
in that row would already have been placed. This is the first rank argument
in Section 6, Lemma 20. -/
theorem rowReference_isLowerRow {n : ℕ} (hn : 0 < n) :
    IsLowerRow (rowReference n) := by
  obtain ⟨i, hi⟩ := q_surjective (rowReference n)
  have hni : n ≤ i := by
    by_contra h
    exact leastUnused_not_mem (occupiedRows n)
      (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hi⟩)
  have hbound := rowReference_le n
  have hne := q_ne_self (show 0 < i by omega)
  exact ⟨i, by omega, hi⟩

/-- The number `t` of lower rows strictly below the current least unused row,
as introduced in Section 6, Lemma 20. This counts all lower rows, not just
those known to be occupied before the current column. -/
noncomputable def referenceLowerRank (n : ℕ) : ℕ := by
  classical
  exact Nat.count IsLowerRow (rowReference n)

/-- The least unused row has zero-based rank `referenceLowerRank n` among
the lower rows, by the rank characterization used in Lemma 20. -/
theorem sortedLowerRow_referenceLowerRank {n : ℕ} (hn : 0 < n) :
    sortedLowerRow (referenceLowerRank n) = rowReference n := by
  classical
  exact Nat.nth_count (rowReference_isLowerRow hn)

/-- The row reference identity `m = t + 1 + U(t)` from Section 6, Lemma 20,
obtained by applying Lemma 4 to the first unused lower row. -/
theorem rowReference_eq_rank_add_count {n : ℕ} (hn : 0 < n) :
    rowReference n = referenceLowerRank n + 1 + upperCount (referenceLowerRank n) := by
  rw [← sortedLowerRow_referenceLowerRank hn, sortedLowerRow_eq q_surjective]

/-- The lower queens strictly before column `n` are counted by `L(n - 1)`.
This connects the local records with the global count in Lemma 20. -/
theorem earlierLowerColumns_card {n : ℕ} (hn : 0 < n) :
    (earlierLowerColumns n).card = lowerCount (n - 1) := by
  rw [← count_lower_eq_lowerCount, Nat.count_eq_card_filter_range]
  congr 1
  rw [Nat.sub_add_cancel hn]
  rfl

/-- Offsetting the retained lower rows does not change their count.
This interprets `|R|` in the rank identity of Section 6, Lemma 20. -/
theorem rowOffsets_card (n : ℕ) :
    (rowOffsets n).card =
      ((earlierLowerColumns n).filter (fun i => rowReference n ≤ q i)).card := by
  apply Finset.card_image_iff.mpr
  intro i hi j hj heq
  change q i - rowReference n = q j - rowReference n at heq
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact q_injective (by omega)

/-- All lower rows below the least unused row have already been occupied.
This finite counting identity is the key interpretation of `t` in Lemma 20. -/
theorem referenceLowerRank_eq_card (n : ℕ) :
    referenceLowerRank n =
      ((earlierLowerColumns n).filter (fun i => q i < rowReference n)).card := by
  classical
  have hsets :
      ((earlierLowerColumns n).filter (fun i => q i < rowReference n)).image q =
        (Finset.range (rowReference n)).filter IsLowerRow := by
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      earlierLowerColumns]
    constructor
    · rintro ⟨i, ⟨⟨hi, hlower⟩, hrow⟩, rfl⟩
      exact ⟨hrow, ⟨i, hlower, rfl⟩⟩
    · rintro ⟨hr, i, hlower, rfl⟩
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp (mem_of_lt_leastUnused hr)
      have hij : j = i := q_injective heq
      subst j
      exact ⟨i, ⟨⟨Finset.mem_range.mp hj, hlower⟩, hr⟩, rfl⟩
  rw [referenceLowerRank, Nat.count_eq_card_filter_range, ← hsets,
    Finset.card_image_of_injective _ q_injective]

/-- The lower rows already used split at the least unused row into `t` rows
below it and the `|R|` retained rows above it: `t + |R| = L(n - 1)`.
This is the second rank identity in Section 6, Lemma 20. -/
theorem referenceLowerRank_add_card_rowOffsets {n : ℕ} (hn : 0 < n) :
    referenceLowerRank n + (rowOffsets n).card = lowerCount (n - 1) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := earlierLowerColumns n) (p := fun i => q i < rowReference n)
  simp only [not_lt] at h
  rw [← referenceLowerRank_eq_card, ← rowOffsets_card, earlierLowerColumns_card hn] at h
  exact h

/-- The recursive argument in Lemma 20 is strictly earlier than `n - 1`
once column one, an upper column, has been filled. -/
theorem referenceLowerRank_lt {n : ℕ} (hn : 2 ≤ n) :
    referenceLowerRank n < n - 1 := by
  have hsplit := referenceLowerRank_add_card_rowOffsets (show 0 < n by omega)
  have hpositive := upperCount_pos (show 0 < n - 1 by omega)
  unfold lowerCount at hsplit
  omega

/-- The local diagonal rank identity gives `U(n - 1) = m + w - |D|`,
the first counting equation in Section 6, Lemma 20. Signed arithmetic avoids
truncated subtraction when the window is negative. -/
theorem upperCount_eq_reference_window {n : ℕ} (hn : 0 < n) :
    (upperCount (n - 1) : ℤ) = (rowReference n : ℤ) + window n -
      ((diagonalOffsets n).card : ℤ) := by
  have hrank := nextLowerRank_eq_reference_add_offsets n
  rw [nextLowerRank, earlierLowerColumns_card hn, lowerCount] at hrank
  have hbounded := upperCount_le (n - 1)
  unfold window
  omega

/-- **Lemma 20 (exact error recursion).** The upper-count error before
column `n` is a contracting affine function of the error at the lower-row
rank of its least unused row. This holds already for every positive column;
`referenceLowerRank_lt` supplies the strict decrease needed in Proposition 21. -/
theorem exact_error_recursion {n : ℕ} (hn : 0 < n) :
    φ ^ 2 * countError upperCount (n - 1) =
      (window n : ℝ) - ((diagonalOffsets n).card : ℝ) -
        φ * ((rowOffsets n).card : ℝ) + 1 +
          countError upperCount (referenceLowerRank n) := by
  have hcount : (upperCount (n - 1) : ℝ) = (rowReference n : ℝ) +
      (window n : ℝ) - ((diagonalOffsets n).card : ℝ) := by
    exact_mod_cast upperCount_eq_reference_window hn
  have hrow : (rowReference n : ℝ) = (referenceLowerRank n : ℝ) + 1 +
      (upperCount (referenceLowerRank n) : ℝ) := by
    exact_mod_cast rowReference_eq_rank_add_count hn
  have hsplit : (referenceLowerRank n : ℝ) + ((rowOffsets n).card : ℝ) =
      ((n - 1 : ℕ) : ℝ) - (upperCount (n - 1) : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ))
      (referenceLowerRank_add_card_rowOffsets hn)
    simpa only [Nat.cast_add, lowerCount, Nat.cast_sub (upperCount_le (n - 1))] using h
  have hinv : φ⁻¹ = φ - 1 := eq_sub_iff_add_eq.mpr goldenRatio_inv_add_one
  simp only [countError, hinv, Real.goldenRatio_sq]
  nlinarith [Real.goldenRatio_sq]

end Queens
