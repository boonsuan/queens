import Queens.Exactness
import Queens.Finite.SharpBounds

/-!
# The sharper inequalities on the actual board

This file transfers Proposition 21's additional finite checks to the greedy
sequence. The represented state gives the bound on `w - |D| - φ |R|` directly.
For the lower-diagonal bound, the actual candidate is retained by the complete
branching calculation, so the bound checked on every lower choice applies to it.
The first thirty columns are checked against the independently verified greedy
prefix. The analytic use of these bounds is separate from the finite checker.
-/

namespace Queens

/-- Proposition 21, record inequality: every actual state from column 30
onwards has `-4 ≤ w - |D| - φ |R| ≤ 1`. -/
theorem sharp_record_bounds (n : ℕ) (hn : 30 ≤ n) :
    -4 ≤ (window n : ℝ) - ((diagonalOffsets n).card : ℝ) -
      Real.goldenRatio * ((rowOffsets n).card : ℝ) ∧
    (window n : ℝ) - ((diagonalOffsets n).card : ℝ) -
      Real.goldenRatio * ((rowOffsets n).card : ℝ) ≤ 1 := by
  obtain ⟨s, hrep, hcert, _⟩ := actualInvariant_of_localStepExact local_step_exact n hn
  rw [hrep.window_eq, hrep.diagonalOffsets_eq, hrep.rowOffsets_eq]
  exact (Finite.certified_sharpRecordCondition hcert).bounds

/-- Proposition 21, finite starting check: every lower queen before column 30
has upper diagonal discrepancy at most two. This check uses the Lean kernel. -/
theorem seed_lower_discrepancy_le_two : ∀ n : Fin 30,
    Finite.seedRow n.val < n.val →
    (n.val : ℤ) - Finite.seedRow n.val -
      (((Finset.range (n.val + 1)).filter (fun i => Finite.seedRow i < i)).card : ℤ) ≤ 2 := by
  decide

/-- Proposition 21, direct starting case: the checked upper discrepancy bound
holds for every actual lower queen before column 30. -/
theorem prefix_lower_discrepancy_le_two {n : ℕ} (hn : n < 30) (hlower : q n < n) :
    (n : ℤ) - q n -
      (((Finset.range (n + 1)).filter (fun i => q i < i)).card : ℤ) ≤ 2 := by
  have hsets : (Finset.range (n + 1)).filter (fun i => q i < i) =
      (Finset.range (n + 1)).filter (fun i => Finite.seedRow i < i) := by
    apply Finset.filter_congr
    intro i hi
    rw [Finite.q_eq_seedRow (by have := Finset.mem_range.mp hi; omega)]
  rw [hsets, Finite.q_eq_seedRow hn]
  exact seed_lower_discrepancy_le_two ⟨n, hn⟩ (by rwa [← Finite.q_eq_seedRow hn])

/-- Proposition 21, local lower-choice inequality: the actual chosen offset
obeys `w - r - |D| ≤ 2` from column 30 onwards. -/
theorem sharp_lower_choice_bound {n : ℕ} (hn : 30 ≤ n) (hlower : q n < n) :
    window n - (rowOffset n : ℤ) - ((diagonalOffsets n).card : ℤ) ≤ 2 := by
  obtain ⟨s, hrep, hcert, hword⟩ := actualInvariant_of_localStepExact local_step_exact n hn
  obtain ⟨next, hnext, _⟩ := Finite.certified_successors hcert
  obtain ⟨queues, choices, hextend, hchoose, _⟩ := Finite.calculate_decompose hnext
  have hchoices : Finite.calculateChoices Finite.Data.historyGraph s = .ok choices := by
    simpa [Finite.calculateChoices, hextend, Bind.bind, Except.bind] using hchoose
  have hm := rowReference_ge_nineteen hn
  obtain ⟨choice, length, _, _, hmatches, hchoice⟩ :=
    local_choices_exact_of_memory (by decide)
      (by simp only [Finite.historyLength]; omega) (countReference_ge_twelve hn)
      hrep (Finite.certified_condition hcert) hword hextend hchoose
  have hbound := Finite.certified_sharpChoiceCondition hcert hchoices hchoice
  have hactual : choice = some (rowOffset n) := by
    simpa only [if_pos hlower] using hmatches.eq_actual
  simp only [Finite.SharpChoiceCondition, hactual] at hbound
  simpa only [hrep.window_eq, hrep.diagonalOffsets_eq] using hbound

/-- Proposition 21: the chronological lower diagonal of positive rank `k+1`
exceeds that rank by at most two. This sharpens the upper half of Lemma 5. -/
theorem lower_diagonal_discrepancy_le_two (k : ℕ) :
    (lowerDiagonal k : ℤ) - ((k : ℤ) + 1) ≤ 2 := by
  have hlower := lowerColumn_lower (infinite_lowerColumns q_surjective) k
  rw [lowerDiagonal_cast]
  by_cases hprefix : lowerColumn k < 30
  · have h := prefix_lower_discrepancy_le_two hprefix hlower
    have hcount : ((Finset.range (lowerColumn k + 1)).filter (fun i => q i < i)).card =
        k + 1 := by
      classical
      rw [← Nat.count_eq_card_filter_range]
      exact Nat.count_nth_succ_of_infinite (infinite_lowerColumns q_surjective) k
    simpa only [hcount, Nat.cast_add, Nat.cast_one] using h
  · have h := sharp_lower_choice_bound (by omega) hlower
    rw [← local_rank_identity hlower, nextLowerRank_lowerColumn] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h

end Queens
