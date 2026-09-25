import Queens.Word
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting upper rows from a retained window

Proposition 13 (Section 4.4) computes the number of upper rows below a threshold
by adjusting the upper-column count at a reference column. This file proves the
finite-set identity on the actual board. The hypotheses say precisely that
omitted old sources lie below the threshold and omitted future sources lie above it.
`LocalGeometry` supplies those exclusions under the hypotheses of Lemma 16.
-/

namespace Queens

/-- The source columns of upper queens whose rows are at most `T`.
Their cardinality is the upper-row count `B(T)` in Section 4.4. -/
noncomputable def upperRowSources (T : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter (fun i => i < q i ∧ q i ≤ T)

/-- The upper-row count `B(T)` in Proposition 13. Distinct sources occupy
distinct rows by the nonattacking condition. -/
noncomputable def upperRowCount (T : ℕ) : ℕ := (upperRowSources T).card

/-- Membership in the upper-row source set, without the redundant column bound.
This is the finite counting interpretation of `B(T)` in Proposition 13. -/
theorem mem_upperRowSources {i T : ℕ} :
    i ∈ upperRowSources T ↔ i < q i ∧ q i ≤ T := by
  simp only [upperRowSources, Finset.mem_filter, Finset.mem_range]
  omega

/-- Upper-row source sets increase with the threshold, as used when taking
the difference `B(n) - B(n - 1)` in Section 4.4. -/
theorem upperRowSources_mono {S T : ℕ} (hST : S ≤ T) :
    upperRowSources S ⊆ upperRowSources T := by
  intro i hi
  rw [mem_upperRowSources] at hi ⊢
  exact ⟨hi.1, hi.2.trans hST⟩

private lemma card_sub_card_eq_differences (S T : Finset ℕ) :
    (S.card : ℤ) - T.card = ((S \ T).card : ℤ) - (T \ S).card := by
  have hS := Finset.card_sdiff_add_card_inter S T
  have hT := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hT
  omega

/-- **Proposition 13 (upper-row count)**, expressed using absolute retained
columns `[a,b)`. Relative offsets turn the two cardinalities into `J(T-m-κ)`.
The old- and future-source hypotheses are exactly the two exclusions required
by the paper's proposition. -/
theorem upperRowCount_eq_adjustment (a m b T : ℕ)
    (hm : 0 < m)
    (hold : ∀ i < a, i < q i → q i ≤ T)
    (hfuture : ∀ i, b ≤ i → i < q i → T < q i) :
    (upperRowCount T : ℤ) = (upperCount (m - 1) : ℤ) +
      (((Finset.Ico m b).filter (fun i => i < q i ∧ q i ≤ T)).card : ℤ) -
      (((Finset.Ico a m).filter (fun i => i < q i ∧ T < q i)).card : ℤ) := by
  classical
  let baseline := (Finset.range m).filter (fun i => i < q i)
  have hbase : baseline.card = upperCount (m - 1) := by
    simp only [baseline, upperCount, Nat.sub_add_cancel hm]
  have hadded : upperRowSources T \ baseline =
      (Finset.Ico m b).filter (fun i => i < q i ∧ q i ≤ T) := by
    ext i
    simp only [Finset.mem_sdiff, mem_upperRowSources, baseline,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hi, hiT⟩, hnot⟩
      have hib : i < b := by
        by_contra h
        have := hfuture i (by omega) hi
        omega
      exact ⟨⟨by omega, hib⟩, hi, hiT⟩
    · rintro ⟨⟨hmi, _⟩, hi, hiT⟩
      exact ⟨⟨hi, hiT⟩, by omega⟩
  have hremoved : baseline \ upperRowSources T =
      (Finset.Ico a m).filter (fun i => i < q i ∧ T < q i) := by
    ext i
    simp only [Finset.mem_sdiff, mem_upperRowSources, baseline,
      Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨him, hi⟩, hnot⟩
      have hai : a ≤ i := by
        by_contra h
        exact hnot ⟨hi, hold i (by omega) hi⟩
      exact ⟨⟨hai, him⟩, hi, by omega⟩
    · rintro ⟨⟨_, him⟩, hi, hiT⟩
      exact ⟨⟨him, hi⟩, by omega⟩
  have hcard := card_sub_card_eq_differences (upperRowSources T) baseline
  rw [hadded, hremoved, hbase] at hcard
  unfold upperRowCount
  omega

/-- Increasing a positive row threshold adds precisely the upper queen in
that row, if there is one. This is `bₙ = B(n) - B(n - 1)` in Section 4.4. -/
theorem upperRowCount_eq_previous_add_bit {n : ℕ} (hn : 0 < n) :
    upperRowCount n = upperRowCount (n - 1) + upperRowBit n := by
  classical
  by_cases hex : ∃ i, i < q i ∧ q i = n
  · obtain ⟨i, hi, hrow⟩ := hex
    have hbit : upperRowBit n = 1 := (upperRowBit_eq_one_iff n).mpr ⟨i, hi, hrow⟩
    have heq : upperRowSources n = insert i (upperRowSources (n - 1)) := by
      ext j
      simp only [mem_upperRowSources, Finset.mem_insert]
      constructor
      · rintro ⟨hj, hjn⟩
        by_cases heq : q j = n
        · exact Or.inl (q_injective (heq.trans hrow.symm))
        · exact Or.inr ⟨hj, by omega⟩
      · rintro (rfl | ⟨hj, hjn⟩)
        · exact ⟨hi, hrow.le⟩
        · exact ⟨hj, by omega⟩
    have hnot : i ∉ upperRowSources (n - 1) := by
      rw [mem_upperRowSources]
      omega
    simp [upperRowCount, heq, Finset.card_insert_of_notMem hnot, hbit]
  · have hbit : upperRowBit n = 0 := by
      have hnot := (upperRowBit_eq_one_iff n).not.mpr hex
      have hle := upperRowBit_le_one n
      omega
    have heq : upperRowSources n = upperRowSources (n - 1) := by
      apply Finset.Subset.antisymm ?_ (upperRowSources_mono (Nat.sub_le _ _))
      intro i hi
      rw [mem_upperRowSources] at hi ⊢
      have hne : q i ≠ n := fun h => hex ⟨i, hi.1, h⟩
      exact ⟨hi.1, by omega⟩
    simp [upperRowCount, heq, hbit]

/-- The output row bit is the signed difference between consecutive upper-row
counts, the final identity in Proposition 13. -/
theorem upperRowBit_eq_count_difference {n : ℕ} (hn : 0 < n) :
    (upperRowBit n : ℤ) = (upperRowCount n : ℤ) - (upperRowCount (n - 1) : ℤ) := by
  have h := upperRowCount_eq_previous_add_bit hn
  omega

end Queens
