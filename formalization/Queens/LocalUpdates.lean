import Queens.LocalAdvances
import Queens.LocalRepresentation

/-!
# Updating the actual offset records

Equation (update), Section 4.5, follows by inserting the new lower queen (when
there is one) and translating the three reference positions. The set-level
identities here are independent of the bit-mask implementation.
-/

namespace Queens

/-- Retain only values at or beyond a reference and subtract that reference.
This is the common operation defining all three local offset records. -/
def retainedOffsets (reference : ℕ) (values : Finset ℕ) : Finset ℕ :=
  (values.filter (fun v => reference ≤ v)).image (fun v => v - reference)

/-- Membership in a translated, truncated set of offsets. -/
theorem mem_retainedOffsets {reference r : ℕ} {values : Finset ℕ} :
    r ∈ retainedOffsets reference values ↔
      ∃ v ∈ values, reference ≤ v ∧ v - reference = r := by
  simp [retainedOffsets, Finset.mem_image, Finset.mem_filter, and_assoc]

/-- Advancing a reference twice is the same as advancing it by the sum.
This is the set-level meaning of successive bit-mask shifts. -/
theorem retainedOffsets_add (a b : ℕ) (values : Finset ℕ) :
    retainedOffsets (a + b) values = retainedOffsets b (retainedOffsets a values) := by
  ext r
  simp only [mem_retainedOffsets]
  constructor
  · rintro ⟨v, hv, hbound, heq⟩
    refine ⟨v - a, ⟨v, hv, by omega, rfl⟩, by omega, ?_⟩
    omega
  · rintro ⟨u, ⟨v, hv, ha, hequ⟩, hb, heqr⟩
    exact ⟨v, hv, by omega, by omega⟩

/-- Inserting a value at or above the reference inserts precisely its offset. -/
theorem retainedOffsets_insert {a v : ℕ} (hv : a ≤ v) (values : Finset ℕ) :
    retainedOffsets a (insert v values) = insert (v - a) (retainedOffsets a values) := by
  simp [retainedOffsets, Finset.filter_insert, hv]

/-- Positive-lower rows already occupied before column `n`. -/
noncomputable def lowerRowsBefore (n : ℕ) : Finset ℕ := (earlierLowerColumns n).image q

/-- Antidiagonal indices of the earlier lower queens. -/
noncomputable def lowerAntidiagonalsBefore (n : ℕ) : Finset ℕ :=
  (earlierLowerColumns n).image (fun i => i + q i)

/-- Normalize `R` as reference subtraction on the set of earlier lower rows. -/
theorem rowOffsets_eq_retained (n : ℕ) :
    rowOffsets n = retainedOffsets (rowReference n) (lowerRowsBefore n) := by
  ext r
  simp only [rowOffsets, mem_retainedOffsets, lowerRowsBefore, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hbound⟩, heq⟩
    exact ⟨q i, ⟨i, hi, rfl⟩, hbound, heq⟩
  · rintro ⟨v, ⟨i, hi, rfl⟩, hbound, heq⟩
    exact ⟨i, ⟨hi, hbound⟩, heq⟩

/-- Normalize `D` as reference subtraction on the earlier lower diagonals. -/
theorem diagonalOffsets_eq_retained (n : ℕ) :
    diagonalOffsets n = retainedOffsets (diagonalReference n) (lowerDiagonals n) := rfl

/-- Normalize `A` as reference subtraction on the earlier lower antidiagonals. -/
theorem antidiagonalOffsets_eq_retained (n : ℕ) :
    antidiagonalOffsets n = retainedOffsets (n + rowReference n) (lowerAntidiagonalsBefore n) := by
  ext r
  simp only [antidiagonalOffsets, mem_retainedOffsets, lowerAntidiagonalsBefore,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hbound⟩, heq⟩
    exact ⟨i + q i, ⟨i, hi, rfl⟩, hbound, heq⟩
  · rintro ⟨v, ⟨i, hi, rfl⟩, hbound, heq⟩
    exact ⟨i, ⟨hi, hbound⟩, heq⟩

/-- The next column adds to the lower-column set exactly for a lower queen. -/
theorem earlierLowerColumns_succ (n : ℕ) :
    earlierLowerColumns (n + 1) =
      if q n < n then insert n (earlierLowerColumns n) else earlierLowerColumns n := by
  unfold earlierLowerColumns
  rw [Finset.range_add_one]
  simp only [Finset.filter_insert]

/-- The temporary row record after inserting the current lower choice. -/
noncomputable def insertedRowOffsets (n : ℕ) : Finset ℕ :=
  if q n < n then insert (rowOffset n) (rowOffsets n) else rowOffsets n

/-- The temporary diagonal record after inserting the current lower choice. -/
noncomputable def insertedDiagonalOffsets (n : ℕ) : Finset ℕ :=
  if q n < n then insert (n - q n - diagonalReference n) (diagonalOffsets n)
    else diagonalOffsets n

/-- The temporary antidiagonal record after inserting the current lower choice. -/
noncomputable def insertedAntidiagonalOffsets (n : ℕ) : Finset ℕ :=
  if q n < n then insert (rowOffset n) (antidiagonalOffsets n) else antidiagonalOffsets n

/-- Insertion into `R` is precisely the new row set measured at the old reference. -/
theorem insertedRowOffsets_eq (n : ℕ) :
    insertedRowOffsets n = retainedOffsets (rowReference n) (lowerRowsBefore (n + 1)) := by
  unfold lowerRowsBefore
  rw [earlierLowerColumns_succ]
  by_cases hn : q n < n
  · rw [if_pos hn, Finset.image_insert, retainedOffsets_insert (rowReference_le_q n)]
    simp only [insertedRowOffsets, if_pos hn, rowOffset, rowOffsets_eq_retained, lowerRowsBefore]
  · simp only [if_neg hn, insertedRowOffsets, rowOffsets_eq_retained, lowerRowsBefore]

/-- Insertion into `D` is precisely the new diagonal set measured at the old reference. -/
theorem insertedDiagonalOffsets_eq (n : ℕ) :
    insertedDiagonalOffsets n = retainedOffsets (diagonalReference n) (lowerDiagonals (n + 1)) := by
  unfold lowerDiagonals
  rw [earlierLowerColumns_succ]
  by_cases hn : q n < n
  · rw [if_pos hn, Finset.image_insert,
      retainedOffsets_insert (diagonalReference_le_lowerDiagonal hn)]
    simp only [insertedDiagonalOffsets, if_pos hn, diagonalOffsets_eq_retained, lowerDiagonals]
  · simp only [if_neg hn, insertedDiagonalOffsets, diagonalOffsets_eq_retained, lowerDiagonals]

/-- Insertion into `A` is precisely the new antidiagonal set measured at the old reference. -/
theorem insertedAntidiagonalOffsets_eq (n : ℕ) :
    insertedAntidiagonalOffsets n =
      retainedOffsets (n + rowReference n) (lowerAntidiagonalsBefore (n + 1)) := by
  unfold lowerAntidiagonalsBefore
  rw [earlierLowerColumns_succ]
  by_cases hn : q n < n
  · have hbound : n + rowReference n ≤ n + q n := Nat.add_le_add_left (rowReference_le_q n) n
    rw [if_pos hn, Finset.image_insert, retainedOffsets_insert hbound]
    simp only [insertedAntidiagonalOffsets, if_pos hn, rowOffset,
      antidiagonalOffsets_eq_retained, lowerAntidiagonalsBefore, Nat.add_sub_add_left]
  · simp only [if_neg hn, insertedAntidiagonalOffsets,
      antidiagonalOffsets_eq_retained, lowerAntidiagonalsBefore]

/-- The actual row-reference advance `μ`, Section 4.5. -/
noncomputable def rowAdvance (n : ℕ) : ℕ := rowReference (n + 1) - rowReference n

/-- The actual lower-diagonal-reference advance `ν`, Section 4.5. -/
noncomputable def lowerDiagonalAdvance (n : ℕ) : ℕ :=
  diagonalReference (n + 1) - diagonalReference n

/-- Advancing by `μ` reaches the next actual row reference. -/
theorem rowReference_add_advance (n : ℕ) :
    rowReference n + rowAdvance n = rowReference (n + 1) := by
  have h := rowReference_mono (show n ≤ n + 1 by omega)
  unfold rowAdvance
  omega

/-- Advancing by `ν` reaches the next actual diagonal reference. -/
theorem diagonalReference_add_advance (n : ℕ) :
    diagonalReference n + lowerDiagonalAdvance n = diagonalReference (n + 1) := by
  have h := diagonalReference_mono (show n ≤ n + 1 by omega)
  unfold lowerDiagonalAdvance
  omega

/-- Equation (update), the actual row record: insert the new lower choice,
then discard and translate offsets by `μ`. -/
theorem rowOffsets_succ (n : ℕ) :
    rowOffsets (n + 1) = retainedOffsets (rowAdvance n) (insertedRowOffsets n) := by
  rw [rowOffsets_eq_retained, insertedRowOffsets_eq, ← retainedOffsets_add,
    rowReference_add_advance]

/-- Equation (update), the actual diagonal record: insert the new lower choice,
then discard and translate offsets by `ν`. -/
theorem diagonalOffsets_succ (n : ℕ) :
    diagonalOffsets (n + 1) =
      retainedOffsets (lowerDiagonalAdvance n) (insertedDiagonalOffsets n) := by
  rw [diagonalOffsets_eq_retained, insertedDiagonalOffsets_eq, ← retainedOffsets_add,
    diagonalReference_add_advance]

/-- Equation (update), the actual antidiagonal record: its reference advances
by `1 + μ`, because both the column and row reference move. -/
theorem antidiagonalOffsets_succ (n : ℕ) :
    antidiagonalOffsets (n + 1) =
      retainedOffsets (1 + rowAdvance n) (insertedAntidiagonalOffsets n) := by
  rw [antidiagonalOffsets_eq_retained, insertedAntidiagonalOffsets_eq, ← retainedOffsets_add]
  have hm := rowReference_add_advance n
  congr 1
  omega

/-- Equation (update), the signed candidate-window width. -/
theorem window_succ (n : ℕ) :
    window (n + 1) = window n + 1 - (rowAdvance n : ℤ) - (lowerDiagonalAdvance n : ℤ) := by
  have hm := rowReference_add_advance n
  have hd := diagonalReference_add_advance n
  unfold window
  omega

/-- Equation (update), the signed upper-count displacement, before rewriting
the count increment as the sum of the consumed column bits. -/
theorem upperDisplacement_succ (n : ℕ) :
    upperDisplacement (n + 1) = upperDisplacement n + 1 - (rowAdvance n : ℤ) -
      ((countReference (n + 1) : ℤ) - (countReference n : ℤ)) := by
  have hm := rowReference_add_advance n
  unfold upperDisplacement
  omega

/-- The upper count increases by the column bit at each positive column. -/
theorem upperCount_eq_pred_add_columnBit {n : ℕ} (hn : 0 < n) :
    upperCount n = upperCount (n - 1) + columnBit n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa [columnBit] using upperCount_succ k

/-- The column bits in a consumed actual word segment record precisely the
increase in the upper count. This supplies `Δu` in equation (update). -/
theorem upperCount_add_segment_sum {m : ℕ} (hm : 0 < m) (length : ℕ) :
    upperCount (m - 1) + ((wordSegment m length).map Finite.upperBit).sum =
      upperCount (m + length - 1) := by
  induction length with
  | zero => simp [wordSegment]
  | succ k ih =>
    rw [wordSegment_add m k 1]
    simp only [List.map_append, List.sum_append]
    have hone : ((wordSegment (m + k) 1).map Finite.upperBit).sum = columnBit (m + k) := by
      simp [wordSegment, upperBit_queenSymbol]
    rw [hone, ← Nat.add_assoc, ih]
    have hstep := upperCount_eq_pred_add_columnBit (show 0 < m + k by omega)
    have hindex : m + (k + 1) - 1 = m + k := by omega
    rw [hindex]
    exact hstep.symm

/-- The upper-count reference changes by the sum of the `μ` consumed
column bits, exactly as Algorithm 1 computes it. -/
theorem countReference_succ {n : ℕ} (hn : 0 < n) :
    countReference (n + 1) = countReference n +
      ((wordSegment (rowReference n) (rowAdvance n)).map Finite.upperBit).sum := by
  have h := upperCount_add_segment_sum (rowReference_pos hn) (rowAdvance n)
  rw [rowReference_add_advance] at h
  exact h.symm

/-- Equation (update), including the word-based computation of `Δu`. -/
theorem upperDisplacement_succ_word {n : ℕ} (hn : 0 < n) :
    upperDisplacement (n + 1) = upperDisplacement n + 1 - (rowAdvance n : ℤ) -
      (((wordSegment (rowReference n) (rowAdvance n)).map Finite.upperBit).sum : ℤ) := by
  have h := countReference_succ hn
  rw [upperDisplacement_succ]
  omega

/-- The temporary row offsets exactly describe lower queens through the
current column, still measured relative to the old row reference. -/
theorem mem_insertedRowOffsets {n r : ℕ} :
    r ∈ insertedRowOffsets n ↔
      ∃ i < n + 1, q i < i ∧ q i = rowReference n + r := by
  rw [insertedRowOffsets_eq, mem_retainedOffsets]
  simp only [lowerRowsBefore, Finset.mem_image, earlierLowerColumns,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨v, ⟨i, ⟨hi, hlower⟩, rfl⟩, hbound, heq⟩
    exact ⟨i, hi, hlower, by omega⟩
  · rintro ⟨i, hi, hlower, hrow⟩
    exact ⟨q i, ⟨i, ⟨hi, hlower⟩, rfl⟩, by omega, by omega⟩

/-- Within the already determined part of the word, a positive row is
occupied precisely when its lower-record bit or upper-row bit is set. -/
theorem occupied_row_iff_inserted_or_upper {n r : ℕ}
    (hpos : 0 < rowReference n + r) (hbound : rowReference n + r ≤ n) :
    rowReference n + r ∈ occupiedRows (n + 1) ↔
      r ∈ insertedRowOffsets n ∨ upperRowBit (rowReference n + r) = 1 := by
  constructor
  · intro hmem
    obtain ⟨i, hi, hrow⟩ := Finset.mem_image.mp hmem
    by_cases hu : i < q i
    · exact Or.inr ((upperRowBit_eq_one_iff _).mpr ⟨i, hu, hrow⟩)
    · have hipos : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        subst i
        simp only [q_zero] at hrow
        omega
      have hlower : q i < i := by have hne := q_ne_self hipos; omega
      exact Or.inl (mem_insertedRowOffsets.mpr
        ⟨i, Finset.mem_range.mp hi, hlower, hrow⟩)
  · rintro (hlower | hupper)
    · obtain ⟨i, hi, _, hrow⟩ := mem_insertedRowOffsets.mp hlower
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hrow⟩
    · obtain ⟨i, hu, hrow⟩ := (upperRowBit_eq_one_iff _).mp hupper
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hrow⟩

/-- The actual advance `μ` is at most six under the bounds used by Lemma 16. -/
theorem rowAdvance_le_six {n : ℕ} (hw : window n ≤ 4)
    (hR : rowOffsets n ⊆ Finset.Icc 1 4) : rowAdvance n ≤ 6 := by
  have h := rowReference_succ_le_add_six hw hR
  unfold rowAdvance
  omega

/-- The actual row search stops at `μ`: its temporary lower-row record and
actual upper-row bit are both zero there (Lemma 16). -/
theorem rowAdvance_free {n : ℕ} (hn : 0 < n) (hw : window n ≤ 4)
    (hR : rowOffsets n ⊆ Finset.Icc 1 4) (hcausal : rowReference n + 6 < n) :
    rowAdvance n ∉ insertedRowOffsets n ∧
      upperRowBit (rowReference n + rowAdvance n) = 0 := by
  have hmu := rowAdvance_le_six hw hR
  have hm := rowReference_pos hn
  have href := rowReference_add_advance n
  have hfree := leastUnused_not_mem (occupiedRows (n + 1))
  change rowReference (n + 1) ∉ occupiedRows (n + 1) at hfree
  rw [← href, occupied_row_iff_inserted_or_upper (by omega) (by omega)] at hfree
  have hbit := upperRowBit_le_one (rowReference n + rowAdvance n)
  constructor
  · exact fun h => hfree (Or.inl h)
  · by_contra h
    have hone : upperRowBit (rowReference n + rowAdvance n) = 1 := by omega
    exact hfree (Or.inr hone)

/-- Every smaller row offset fails the temporary-record/upper-bit search.
Together with `rowAdvance_free`, this identifies its least successful offset. -/
theorem rowAdvance_minimal {n r : ℕ} (hn : 0 < n) (hw : window n ≤ 4)
    (hR : rowOffsets n ⊆ Finset.Icc 1 4) (hcausal : rowReference n + 6 < n)
    (hr : r < rowAdvance n) :
    r ∈ insertedRowOffsets n ∨ upperRowBit (rowReference n + r) = 1 := by
  have hmu := rowAdvance_le_six hw hR
  have hm := rowReference_pos hn
  have href := rowReference_add_advance n
  have hmem : rowReference n + r ∈ occupiedRows (n + 1) :=
    mem_of_lt_leastUnused (by change rowReference n + r < rowReference (n + 1); omega)
  exact (occupied_row_iff_inserted_or_upper (by omega) (by omega)).mp hmem

/-- The actual diagonal advance `ν` is the first unused temporary diagonal
offset. This is the mathematical specification of `diagonalAdvance`. -/
theorem lowerDiagonalAdvance_free (n : ℕ) :
    lowerDiagonalAdvance n ∉ insertedDiagonalOffsets n := by
  rw [insertedDiagonalOffsets_eq, mem_retainedOffsets]
  rintro ⟨v, hv, hbound, heq⟩
  have href := diagonalReference_add_advance n
  have heqv : v = diagonalReference (n + 1) := by omega
  exact diagonalReference_not_mem (n + 1) (heqv ▸ hv)

/-- Every diagonal offset below `ν` is occupied in the temporary record. -/
theorem lowerDiagonalAdvance_minimal {n r : ℕ} (hr : r < lowerDiagonalAdvance n) :
    r ∈ insertedDiagonalOffsets n := by
  rw [insertedDiagonalOffsets_eq, mem_retainedOffsets]
  have href := diagonalReference_add_advance n
  have hdpos := diagonalReference_pos n
  refine ⟨diagonalReference n + r, ?_, by omega, by omega⟩
  apply mem_lowerDiagonals_of_lt_reference (by omega)
  omega

end Queens
