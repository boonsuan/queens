import Queens.LocalBoard
import Queens.Word

/-!
# The actual lower candidates and their attack records

Sections 4.1 and 5 restrict available lower squares to the interval between
the least unused row and the least unused lower diagonal. This file proves
that restriction directly from the greedy board, and verifies that the
actual records `R`, `D`, and `A` detect precisely the attacks from earlier
lower queens. These facts are independent of the finite-state verifier.
-/

namespace Queens

/-- An available square cannot use any previously occupied row. -/
theorem available_not_mem_occupiedRows {n y : ℕ}
    (havailable : Available n y (fun i => q i.val)) : y ∉ occupiedRows n := by
  intro hmem
  obtain ⟨i, hi, hy⟩ := Finset.mem_image.mp hmem
  exact (havailable ⟨i, Finset.mem_range.mp hi⟩).1 hy.symm

/-- The least unused row is a lower bound for every available square,
as used in Section 4.1 to restrict the candidate window. -/
theorem rowReference_le_of_available {n y : ℕ}
    (havailable : Available n y (fun i => q i.val)) : rowReference n ≤ y :=
  leastUnused_le_of_not_mem (available_not_mem_occupiedRows havailable)

/-- An available lower square lies on an unused positive lower diagonal. -/
theorem available_lowerDiagonal_not_mem {n y : ℕ} (hlower : y < n)
    (havailable : Available n y (fun i => q i.val)) :
    n - y ∉ lowerDiagonals n := by
  intro hmem
  obtain ⟨i, hi, hdiag⟩ := Finset.mem_image.mp hmem
  have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hiq := (Finset.mem_filter.mp hi).2
  have hsafe := (havailable ⟨i, hin⟩).2.1
  change y + i ≠ q i + n at hsafe
  omega

/-- The least unused positive lower diagonal bounds every available lower
square, giving the right endpoint `n - d` in Section 4.1. -/
theorem diagonalReference_le_of_available {n y : ℕ} (hlower : y < n)
    (havailable : Available n y (fun i => q i.val)) :
    diagonalReference n ≤ n - y := by
  apply leastUnused_le_of_not_mem
  intro hmem
  rcases Finset.mem_insert.mp hmem with hzero | hused
  · omega
  · exact available_lowerDiagonal_not_mem hlower havailable hused

/-- Every available lower row belongs to the candidate interval `[m, n-d]`
of Section 4.1. This statement concerns all available rows, not just `q n`. -/
theorem available_lower_in_window {n y : ℕ} (hlower : y < n)
    (havailable : Available n y (fun i => q i.val)) :
    rowReference n ≤ y ∧ y ≤ n - diagonalReference n ∧
      ((y - rowReference n : ℕ) : ℤ) ≤ window n := by
  have hm := rowReference_le_of_available havailable
  have hd := diagonalReference_le_of_available hlower havailable
  refine ⟨hm, ?_, ?_⟩
  · omega
  · unfold window
    omega

/-- Every offset in the candidate window gives a square strictly below the
main diagonal; positivity of the least unused diagonal is essential here. -/
theorem candidate_row_lt {n r : ℕ} (hr : (r : ℤ) ≤ window n) :
    rowReference n + r < n := by
  have hd := diagonalReference_pos n
  unfold window at hr
  omega

/-- A negative candidate width forces an upper queen in every positive
column, as stated in Section 4.1. -/
theorem upper_of_window_neg {n : ℕ} (hn : 0 < n) (hw : window n < 0) : n < q n := by
  have hne := q_ne_self hn
  by_contra hnot
  have hlower : q n < n := by omega
  have hoffset := rowOffset_le_window hlower
  omega

/-- The row record `R` detects exactly the earlier lower queens sharing a
candidate's row, the first attack test in Section 4.1. -/
theorem mem_rowOffsets_iff (n r : ℕ) :
    r ∈ rowOffsets n ↔ ∃ i < n, q i < i ∧ q i = rowReference n + r := by
  constructor
  · intro h
    obtain ⟨i, hi, hr⟩ := Finset.mem_image.mp h
    obtain ⟨hicol, hreference⟩ := Finset.mem_filter.mp hi
    obtain ⟨hin, hlower⟩ := Finset.mem_filter.mp hicol
    exact ⟨i, Finset.mem_range.mp hin, hlower, by omega⟩
  · rintro ⟨i, hin, hlower, hrow⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, by omega⟩, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, hlower⟩

/-- The antidiagonal record `A` detects exactly the earlier lower queens
sharing a candidate's antidiagonal, the third attack test in Section 4.1. -/
theorem mem_antidiagonalOffsets_iff (n r : ℕ) :
    r ∈ antidiagonalOffsets n ↔
      ∃ i < n, q i < i ∧ i + q i = n + (rowReference n + r) := by
  constructor
  · intro h
    obtain ⟨i, hi, hr⟩ := Finset.mem_image.mp h
    obtain ⟨hicol, hreference⟩ := Finset.mem_filter.mp hi
    obtain ⟨hin, hlower⟩ := Finset.mem_filter.mp hicol
    exact ⟨i, Finset.mem_range.mp hin, hlower, by omega⟩
  · rintro ⟨i, hin, hlower, hanti⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, by omega⟩, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, hlower⟩

/-- The diagonal record `D` detects exactly the earlier lower queens
sharing a candidate's diagonal, the second attack test in Section 4.1.
The conversion to a natural offset is valid because `r ≤ w`. -/
theorem mem_diagonalOffsets_iff {n r : ℕ} (hr : (r : ℤ) ≤ window n) :
    (window n - (r : ℤ)).toNat ∈ diagonalOffsets n ↔
      ∃ i < n, q i < i ∧ (rowReference n + r) + i = q i + n := by
  have hd := diagonalReference_pos n
  have hrow := candidate_row_lt hr
  constructor
  · intro h
    obtain ⟨k, hk, hoffset⟩ := Finset.mem_image.mp h
    obtain ⟨hkused, hreference⟩ := Finset.mem_filter.mp hk
    obtain ⟨i, hi, hdiag⟩ := Finset.mem_image.mp hkused
    obtain ⟨hin, hlower⟩ := Finset.mem_filter.mp hi
    refine ⟨i, Finset.mem_range.mp hin, hlower, ?_⟩
    unfold window at hr hoffset
    omega
  · rintro ⟨i, hin, hlower, hdiag⟩
    apply Finset.mem_image.mpr
    refine ⟨i - q i, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, hlower⟩, rfl⟩
    · unfold window at hr
      omega
    · unfold window at hr ⊢
      omega

/-- Offset zero never occurs in `R`: its reference is the least unused row. -/
theorem zero_not_mem_rowOffsets (n : ℕ) : 0 ∉ rowOffsets n := by
  rw [mem_rowOffsets_iff]
  rintro ⟨i, hin, _, hrow⟩
  apply leastUnused_not_mem (occupiedRows n)
  change rowReference n ∈ occupiedRows n
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hin, by simpa using hrow⟩

/-- Offset zero never occurs in `D`: its reference is an unused lower diagonal. -/
theorem zero_not_mem_diagonalOffsets (n : ℕ) : 0 ∉ diagonalOffsets n := by
  intro h
  obtain ⟨k, hk, hoffset⟩ := Finset.mem_image.mp h
  obtain ⟨hused, hreference⟩ := Finset.mem_filter.mp hk
  have heq : k = diagonalReference n := by omega
  exact diagonalReference_not_mem n (heq ▸ hused)

/-- The five attack tests for a lower candidate in Sections 4.1–4.4.
The last test still ranges over actual upper queens; restricting it to the
retained history and queue is a separate sufficiency argument in Lemma 16. -/
def LowerCandidateClear (n r : ℕ) : Prop :=
  r ∉ rowOffsets n ∧
  (window n - (r : ℤ)).toNat ∉ diagonalOffsets n ∧
  r ∉ antidiagonalOffsets n ∧
  upperRowBit (rowReference n + r) = 0 ∧
  ¬ ∃ i < n, i < q i ∧ i + q i = n + (rowReference n + r)

/-- A lower candidate is available exactly when all five local attack tests
pass. This includes the origin and the impossibility of an upper queen
attacking a lower square along a diagonal, as required by Lemma 16. -/
theorem available_candidate_iff {n r : ℕ} (hn : 0 < n) (hr : (r : ℤ) ≤ window n) :
    Available n (rowReference n + r) (fun i => q i.val) ↔ LowerCandidateClear n r := by
  have hrow := candidate_row_lt hr
  have hm := rowReference_pos hn
  constructor
  · intro havailable
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hmem
      obtain ⟨i, hin, _, hattack⟩ := (mem_rowOffsets_iff n r).mp hmem
      exact (havailable ⟨i, hin⟩).1 hattack.symm
    · intro hmem
      obtain ⟨i, hin, _, hattack⟩ := (mem_diagonalOffsets_iff hr).mp hmem
      exact (havailable ⟨i, hin⟩).2.1 hattack
    · intro hmem
      obtain ⟨i, hin, _, hattack⟩ := (mem_antidiagonalOffsets_iff n r).mp hmem
      have hsafe := (havailable ⟨i, hin⟩).2.2
      change rowReference n + r + n ≠ q i + i at hsafe
      omega
    · have hbit := upperRowBit_le_one (rowReference n + r)
      by_contra hzero
      have hone : upperRowBit (rowReference n + r) = 1 := by omega
      obtain ⟨i, hi, hirow⟩ := (upperRowBit_eq_one_iff _).mp hone
      have hin : i < n := by omega
      exact (havailable ⟨i, hin⟩).1 hirow.symm
    · rintro ⟨i, hin, _, hattack⟩
      have hsafe := (havailable ⟨i, hin⟩).2.2
      change rowReference n + r + n ≠ q i + i at hsafe
      omega
  · rintro ⟨hR, hD, hA, hbit, hupperAnti⟩ i
    change rowReference n + r ≠ q i.val ∧
      (rowReference n + r) + i.val ≠ q i.val + n ∧
      (rowReference n + r) + n ≠ q i.val + i.val
    have hin := i.isLt
    by_cases hi0 : i.val = 0
    · simp only [hi0, q_zero]
      omega
    · have hne := q_ne_self (show 0 < i.val by omega)
      by_cases hlower : q i.val < i.val
      · refine ⟨?_, ?_, ?_⟩
        · intro hattack
          exact hR ((mem_rowOffsets_iff n r).mpr ⟨i.val, hin, hlower, hattack.symm⟩)
        · intro hattack
          exact hD ((mem_diagonalOffsets_iff hr).mpr ⟨i.val, hin, hlower, hattack⟩)
        · intro hattack
          apply hA
          exact (mem_antidiagonalOffsets_iff n r).mpr ⟨i.val, hin, hlower, by omega⟩
      · have hupper : i.val < q i.val := by omega
        refine ⟨?_, ?_, ?_⟩
        · intro hattack
          have hone := (upperRowBit_eq_one_iff (rowReference n + r)).mpr
            ⟨i.val, hupper, hattack.symm⟩
          omega
        · omega
        · intro hattack
          exact hupperAnti ⟨i.val, hin, hupper, by omega⟩

/-- The actual lower choice is precisely the first candidate passing the
five tests. This proves the candidate-selection part of Lemma 16 without
assuming that the finite calculation already represents the greedy board. -/
theorem q_eq_candidate_iff {n r : ℕ} (hn : 0 < n) (hr : (r : ℤ) ≤ window n) :
    q n = rowReference n + r ↔
      LowerCandidateClear n r ∧ ∀ s < r, ¬ LowerCandidateClear n s := by
  constructor
  · intro hq
    constructor
    · apply (available_candidate_iff hn hr).mp
      simpa only [← hq] using q_available n
    · intro s hs hclear
      have hswindow : (s : ℤ) ≤ window n := by omega
      have hle := q_le_of_available ((available_candidate_iff hn hswindow).mpr hclear)
      omega
  · rintro ⟨hclear, hfirst⟩
    have hle := q_le_of_available ((available_candidate_iff hn hr).mpr hclear)
    have hm := rowReference_le_q n
    by_contra hne
    have hoffset : q n - rowReference n < r := by omega
    have hoffsetWindow : ((q n - rowReference n : ℕ) : ℤ) ≤ window n := by omega
    apply hfirst (q n - rowReference n) hoffset
    apply (available_candidate_iff hn hoffsetWindow).mp
    simpa only [Nat.add_sub_of_le hm] using q_available n

/-- The actual queen is upper exactly when no offset in the lower-candidate
window passes the five tests, including when the window has negative width. -/
theorem q_upper_iff_no_clear_candidate {n : ℕ} (hn : 0 < n) :
    n < q n ↔ ∀ r : ℕ, (r : ℤ) ≤ window n → ¬ LowerCandidateClear n r := by
  constructor
  · intro hupper r hr hclear
    have hle := q_le_of_available ((available_candidate_iff hn hr).mpr hclear)
    have hrow := candidate_row_lt hr
    omega
  · intro hnone
    have hne := q_ne_self hn
    by_contra hnot
    have hlower : q n < n := by omega
    apply hnone (rowOffset n) (rowOffset_le_window hlower)
    apply (available_candidate_iff hn (rowOffset_le_window hlower)).mp
    have hrow : rowReference n + rowOffset n = q n :=
      Nat.add_sub_of_le (rowReference_le_q n)
    rw [hrow]
    exact q_available n

end Queens
