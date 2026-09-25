import Queens.Greedy
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Int

/-!
# Local records of the actual greedy board

Section 4.1 defines a least unused row and positive lower diagonal, together
with offset records. These definitions use the actual sequence `Queens.q`.
The local rank identity and the extraction of diagonal discrepancy from
Condition 15 are proved here. Preservation of Condition 15 by Algorithm 1
is a separate obligation.
-/

namespace Queens

/-- A finite set of natural numbers leaves some natural number unused. -/
theorem exists_not_mem_finset (s : Finset ℕ) : ∃ r, r ∉ s := by
  refine ⟨s.sup id + 1, ?_⟩
  intro h
  have hle := Finset.le_sup (f := id) h
  dsimp only [id_eq] at hle
  omega

/-- Least natural number outside a finite set; used for the two reference
positions of the actual local state in Section 4.1. -/
noncomputable def leastUnused (s : Finset ℕ) : ℕ := Nat.find (exists_not_mem_finset s)

/-- The least unused position is not already occupied. -/
theorem leastUnused_not_mem (s : Finset ℕ) : leastUnused s ∉ s :=
  Nat.find_spec (exists_not_mem_finset s)

/-- Every smaller position than the reference is occupied. -/
theorem mem_of_lt_leastUnused {s : Finset ℕ} {r : ℕ} (hr : r < leastUnused s) : r ∈ s := by
  have h := Nat.find_min (exists_not_mem_finset s) hr
  simpa only [not_not] using h

/-- Any unused position lies at or after the reference. -/
theorem leastUnused_le_of_not_mem {s : Finset ℕ} {r : ℕ} (hr : r ∉ s) :
    leastUnused s ≤ r := Nat.find_min' _ hr

/-- Rows occupied strictly before column `n`. -/
noncomputable def occupiedRows (n : ℕ) : Finset ℕ := (Finset.range n).image q

/-- The least unused row `m` before column `n`, from Section 4.1. -/
noncomputable def rowReference (n : ℕ) : ℕ := leastUnused (occupiedRows n)

/-- Columns containing a lower queen strictly before column `n`. -/
noncomputable def earlierLowerColumns (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => q i < i)

/-- Positive lower-diagonal magnitudes already occupied before column `n`. -/
noncomputable def lowerDiagonals (n : ℕ) : Finset ℕ :=
  (earlierLowerColumns n).image (fun i => i - q i)

/-- The least unused positive lower-diagonal magnitude `d` in Section 4.1.
Inserting zero makes ordinary least-excluded-value search positive. -/
noncomputable def diagonalReference (n : ℕ) : ℕ :=
  leastUnused (insert 0 (lowerDiagonals n))

/-- Signed width `w = n - m - d` of the candidate window, equation (window). -/
noncomputable def window (n : ℕ) : ℤ :=
  (n : ℤ) - (rowReference n : ℤ) - (diagonalReference n : ℤ)

/-- Upper-count reference `κ = U(m-1)` for the actual board, Section 4.2. -/
noncomputable def countReference (n : ℕ) : ℕ := upperCount (rowReference n - 1)

/-- Signed upper-record displacement `z = n - m - κ`, Definition 10. -/
noncomputable def upperDisplacement (n : ℕ) : ℤ :=
  (n : ℤ) - (rowReference n : ℤ) - (countReference n : ℤ)

/-- The actual row-offset record `R` from equation (sets). -/
noncomputable def rowOffsets (n : ℕ) : Finset ℕ :=
  ((earlierLowerColumns n).filter (fun i => rowReference n ≤ q i)).image
    (fun i => q i - rowReference n)

/-- The actual lower-diagonal-offset record `D` from equation (sets). -/
noncomputable def diagonalOffsets (n : ℕ) : Finset ℕ :=
  ((lowerDiagonals n).filter (fun k => diagonalReference n ≤ k)).image
    (fun k => k - diagonalReference n)

/-- The actual antidiagonal-offset record `A` from equation (sets). -/
noncomputable def antidiagonalOffsets (n : ℕ) : Finset ℕ :=
  ((earlierLowerColumns n).filter (fun i => n + rowReference n ≤ i + q i)).image
    (fun i => i + q i - (n + rowReference n))

/-- The positive chronological rank the next lower queen would have:
one more than the number of preceding lower queens. -/
noncomputable def nextLowerRank (n : ℕ) : ℕ := (earlierLowerColumns n).card + 1

/-- The row selected by the greedy rule has not appeared earlier. -/
theorem q_not_mem_occupiedRows (n : ℕ) : q n ∉ occupiedRows n := by
  intro h
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
  have hil : i < n := Finset.mem_range.mp hi
  exact (q_safe hil).1 heq.symm

/-- Every chosen row is at or above the least unused row. -/
theorem rowReference_le_q (n : ℕ) : rowReference n ≤ q n :=
  leastUnused_le_of_not_mem (q_not_mem_occupiedRows n)

/-- After the origin has been placed, the row reference is positive. -/
theorem rowReference_pos {n : ℕ} (hn : 0 < n) : 0 < rowReference n := by
  have hzero : 0 ∈ occupiedRows n := by
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, q_zero⟩
  have h := leastUnused_not_mem (occupiedRows n)
  change rowReference n ∉ occupiedRows n at h
  by_contra hpos
  have heq : rowReference n = 0 := by omega
  exact h (heq ▸ hzero)

/-- Every used lower-diagonal magnitude is positive. -/
theorem lowerDiagonal_pos {n k : ℕ} (hk : k ∈ lowerDiagonals n) : 0 < k := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  have hlower := (Finset.mem_filter.mp hi).2
  omega

/-- The main diagonal is not one of the positive lower diagonals. -/
theorem zero_not_mem_lowerDiagonals (n : ℕ) : 0 ∉ lowerDiagonals n := by
  intro h
  have := lowerDiagonal_pos h
  omega

/-- The lower-diagonal reference is always positive. -/
theorem diagonalReference_pos (n : ℕ) : 0 < diagonalReference n := by
  have h := leastUnused_not_mem (insert 0 (lowerDiagonals n))
  change diagonalReference n ∉ insert 0 (lowerDiagonals n) at h
  by_contra hpos
  have heq : diagonalReference n = 0 := by omega
  exact h (by simp [heq])

/-- The reference lower diagonal is unused. -/
theorem diagonalReference_not_mem (n : ℕ) : diagonalReference n ∉ lowerDiagonals n := by
  exact fun h => leastUnused_not_mem _ (Finset.mem_insert_of_mem h)

/-- Every positive lower diagonal below the reference is occupied. -/
theorem mem_lowerDiagonals_of_lt_reference {n k : ℕ}
    (hk : 0 < k) (hkd : k < diagonalReference n) : k ∈ lowerDiagonals n := by
  have h := mem_of_lt_leastUnused hkd
  rcases Finset.mem_insert.mp h with heq | hmem
  · omega
  · exact hmem

/-- Earlier lower queens have distinct lower-diagonal magnitudes. -/
theorem lowerDiagonal_injOn (n : ℕ) :
    Set.InjOn (fun i => i - q i) (earlierLowerColumns n) := by
  intro i hi j hj h
  change i - q i = j - q j at h
  have hiq := (Finset.mem_filter.mp hi).2
  have hjq := (Finset.mem_filter.mp hj).2
  apply q_diagonal_injective
  change (q i : ℤ) - (i : ℤ) = (q j : ℤ) - (j : ℤ)
  omega

/-- Counting occupied lower diagonals counts exactly the earlier lower queens. -/
theorem lowerDiagonals_card (n : ℕ) :
    (lowerDiagonals n).card = (earlierLowerColumns n).card := by
  exact Finset.card_image_iff.mpr (lowerDiagonal_injOn n)

/-- The occupied lower magnitudes below `d` are exactly `1, …, d-1`. -/
theorem lowerDiagonals_below_reference (n : ℕ) :
    (lowerDiagonals n).filter (fun k => k < diagonalReference n) =
      Finset.Ico 1 (diagonalReference n) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hmem, hlt⟩
    exact ⟨lowerDiagonal_pos hmem, hlt⟩
  · rintro ⟨hpos, hlt⟩
    exact ⟨mem_lowerDiagonals_of_lt_reference hpos hlt, hlt⟩

/-- Offsetting the retained diagonal magnitudes preserves their cardinality. -/
theorem diagonalOffsets_card (n : ℕ) :
    (diagonalOffsets n).card =
      ((lowerDiagonals n).filter (fun k => diagonalReference n ≤ k)).card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  change a - diagonalReference n = b - diagonalReference n at hab
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  omega

/-- The first identity in equation (local-rank): the next lower rank is
`j = d + |D|`, because precisely `d-1` smaller magnitudes have been used. -/
theorem nextLowerRank_eq_reference_add_offsets (n : ℕ) :
    nextLowerRank n = diagonalReference n + (diagonalOffsets n).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := lowerDiagonals n) (p := fun k => k < diagonalReference n)
  rw [lowerDiagonals_below_reference, Nat.card_Ico] at hsplit
  simp only [not_lt] at hsplit
  rw [← diagonalOffsets_card, lowerDiagonals_card] at hsplit
  have hpos := diagonalReference_pos n
  unfold nextLowerRank
  omega

/-- A newly placed lower queen uses a previously unused lower diagonal. -/
theorem q_lowerDiagonal_not_mem {n : ℕ} (hn : q n < n) :
    n - q n ∉ lowerDiagonals n := by
  intro hmem
  obtain ⟨i, hi, hdiag⟩ := Finset.mem_image.mp hmem
  have hil : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hiq := (Finset.mem_filter.mp hi).2
  have hsafe := (q_safe hil).2.1
  omega

/-- The diagonal of a lower placement lies at or beyond the current
least unused lower-diagonal reference. -/
theorem diagonalReference_le_lowerDiagonal {n : ℕ} (hn : q n < n) :
    diagonalReference n ≤ n - q n := by
  apply leastUnused_le_of_not_mem
  intro hmem
  rcases Finset.mem_insert.mp hmem with hzero | hused
  · omega
  · exact q_lowerDiagonal_not_mem hn hused

/-- The actual offset of a new queen from the least unused row. For a
lower queen it is one of the candidate offsets in Section 4.1. -/
noncomputable def rowOffset (n : ℕ) : ℕ := q n - rowReference n

/-- A lower placement's offset lies in the candidate window `0 ≤ r ≤ w`. -/
theorem rowOffset_le_window {n : ℕ} (hn : q n < n) : (rowOffset n : ℤ) ≤ window n := by
  have hm := rowReference_le_q n
  have hd := diagonalReference_le_lowerDiagonal hn
  unfold rowOffset window
  omega

/-- Equation (local-rank): the lower-diagonal discrepancy is exactly
`w - r - |D|`, with all records defined from the actual greedy board. -/
theorem local_rank_identity {n : ℕ} (_hn : q n < n) :
    (n : ℤ) - (q n : ℤ) - (nextLowerRank n : ℤ) =
      window n - (rowOffset n : ℤ) - ((diagonalOffsets n).card : ℤ) := by
  have hm := rowReference_le_q n
  have hrank := nextLowerRank_eq_reference_add_offsets n
  unfold window rowOffset
  omega

/-- The portion of Condition 15 used for diagonal discrepancy:
`w ≤ 4` and `D ⊆ {1,2,3,4}`. The remaining bounds ensure sufficiency
of the local step but are not needed for this arithmetic consequence. -/
def DiagonalRecordBounds (n : ℕ) : Prop :=
  window n ≤ 4 ∧ diagonalOffsets n ⊆ Finset.Icc 1 4

/-- Extraction of Lemma 5 from the actual-record bounds, as in Section 6.4.
This theorem does not assume that an abstract finite state is the actual board. -/
theorem discrepancy_of_record_bounds {n : ℕ} (hn : q n < n)
    (hbounds : DiagonalRecordBounds n) :
    |(n : ℤ) - (q n : ℤ) - (nextLowerRank n : ℤ)| ≤ 4 := by
  rw [local_rank_identity hn, abs_le]
  have hwindow := rowOffset_le_window hn
  have hcard : (diagonalOffsets n).card ≤ 4 := by
    have h := Finset.card_le_card hbounds.2
    simpa using h
  have hw := hbounds.1
  constructor <;> omega

end Queens
