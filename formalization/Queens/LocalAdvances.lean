import Queens.LocalBoard

/-!
# Advances of the actual reference positions

These lemmas formalize the row-search bound in Section 5, Lemma 16. Under
the bounds on `w` and `R`, the two rows at offsets five and six cannot both
be occupied, because only upper queens could occupy them and upper rows
are never adjacent.
-/

namespace Queens

/-- Enlarging a set of occupied positions can only increase its first gap. -/
theorem leastUnused_mono {s t : Finset ℕ} (hst : s ⊆ t) : leastUnused s ≤ leastUnused t := by
  by_contra h
  have hmem := mem_of_lt_leastUnused (s := s) (r := leastUnused t) (by omega)
  exact leastUnused_not_mem t (hst hmem)

/-- The row reference never moves backwards as new queens are placed. -/
theorem rowReference_mono : Monotone rowReference := by
  intro m n hmn
  apply leastUnused_mono
  exact Finset.image_subset_image (Finset.range_mono hmn)

/-- The lower-diagonal reference never moves backwards. -/
theorem diagonalReference_mono : Monotone diagonalReference := by
  intro m n hmn
  apply leastUnused_mono
  apply Finset.insert_subset_insert
  apply Finset.image_subset_image
  exact Finset.filter_subset_filter _ (Finset.range_mono hmn)

/-- A row occupied before the next column and at least five positions beyond
`m` can contain only an upper queen when the actual row/window bounds hold. -/
theorem far_occupied_row_is_upper {n t i : ℕ}
    (hw : window n ≤ 4) (hR : rowOffsets n ⊆ Finset.Icc 1 4)
    (ht : 5 ≤ t) (hi : i < n + 1) (hrow : q i = rowReference n + t) : i < q i := by
  by_contra hupper
  have hle : q i ≤ i := by omega
  have hipos : 0 < i := by
    by_contra h
    have hiz : i = 0 := by omega
    simp [hiz] at hrow
    omega
  have hlower : q i < i := by
    have hne := q_ne_self hipos
    omega
  by_cases hin : i < n
  · have hiLower : i ∈ earlierLowerColumns n :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, hlower⟩
    have htR : t ∈ rowOffsets n := by
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨hiLower, by omega⟩, ?_⟩
      omega
    have hbound := Finset.mem_Icc.mp (hR htR)
    omega
  · have heq : i = n := by omega
    subst i
    have hoff := rowOffset_le_window hlower
    unfold rowOffset at hoff
    omega

/-- The rows at offsets five and six cannot both be occupied after the next
queen is placed. This is the upper-row spacing argument in Lemma 16. -/
theorem one_far_row_unused {n : ℕ} (hw : window n ≤ 4)
    (hR : rowOffsets n ⊆ Finset.Icc 1 4) :
    rowReference n + 5 ∉ occupiedRows (n + 1) ∨
      rowReference n + 6 ∉ occupiedRows (n + 1) := by
  by_contra h
  push Not at h
  obtain ⟨i, hi, hrowi⟩ := Finset.mem_image.mp h.1
  obtain ⟨j, hj, hrowj⟩ := Finset.mem_image.mp h.2
  have hupperi := far_occupied_row_is_upper hw hR (by omega : 5 ≤ 5)
    (Finset.mem_range.mp hi) hrowi
  have hupperj := far_occupied_row_is_upper hw hR (by omega : 5 ≤ 6)
    (Finset.mem_range.mp hj) hrowj
  rcases lt_trichotomy i j with hij | hij | hij
  · have hgap := upper_rows_gap hupperi hupperj hij
    omega
  · subst j
    omega
  · have hgap := upper_rows_gap hupperj hupperi hij
    omega

/-- **Lemma 16(iii), actual reference bound.** With the row and window parts
of Condition 15, the actual least-unused-row reference advances by at most six. -/
theorem rowReference_succ_le_add_six {n : ℕ} (hw : window n ≤ 4)
    (hR : rowOffsets n ⊆ Finset.Icc 1 4) :
    rowReference (n + 1) ≤ rowReference n + 6 := by
  rcases one_far_row_unused hw hR with hfive | hsix
  · have h := leastUnused_le_of_not_mem hfive
    change rowReference (n + 1) ≤ rowReference n + 5 at h
    omega
  · exact leastUnused_le_of_not_mem hsix

end Queens
