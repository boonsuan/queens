import Queens.Exactness

/-!
# Every signed diagonal contains exactly one queen

Corollary 18 follows from two unbounded references. The golden-ratio count
estimate makes the upper count unbounded. For lower diagonals, the certified
bound `|D| ≤ 4` and the identity `j = d + |D|` make the least unused magnitude
unbounded as chronological lower rank increases. The nonattacking property
supplies uniqueness on every diagonal.
-/

namespace Queens

open scoped goldenRatio

/-- The upper count is unbounded, as used in Corollary 18. The proved
golden-ratio estimate supplies an upper rank beyond any prescribed bound. -/
theorem upperCount_unbounded (k : ℕ) : ∃ n, k ≤ upperCount n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((k : ℝ) * φ + 5)
  have hinv : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hcount := upperCount_error_of_diagonalDiscrepancy bounded_diagonal_discrepancy n
  norm_num only [Nat.cast_ofNat] at hcount
  have hlow := (abs_lt.mp hcount).1
  unfold countError at hlow
  have hscaled := mul_lt_mul_of_pos_left hn hinv
  have hcancel : φ⁻¹ * ((k : ℝ) * φ + 5) = (k : ℝ) + φ⁻¹ * 5 := by
    rw [mul_add, mul_left_comm φ⁻¹ (k : ℝ) φ,
      inv_mul_cancel₀ Real.goldenRatio_ne_zero, mul_one]
  rw [hcancel] at hscaled
  refine ⟨n, ?_⟩
  have hreal : (k : ℝ) < (upperCount n : ℝ) := by linarith
  exact_mod_cast hreal.le

/-- Every positive upper diagonal is occupied. Lemma 2 identifies upper
diagonals with upper ranks, and the upper count reaches every such rank. -/
theorem exists_upper_diagonal (k : ℕ) (hk : 0 < k) :
    ∃ n, n < q n ∧ (q n : ℤ) - (n : ℤ) = (k : ℤ) := by
  obtain ⟨n, hcount⟩ := upperCount_unbounded k
  obtain ⟨i, _, hi, hrank⟩ := upperCount_rank_exists hk hcount
  have hrow := q_eq_add_upperCount hi
  exact ⟨i, hi, by omega⟩

/-- Every positive lower-diagonal magnitude is occupied. The finite invariant
keeps at most four used magnitudes above the least unused magnitude; hence the
reference eventually passes every fixed positive magnitude (Corollary 18). -/
theorem exists_lower_diagonal (d : ℕ) (hd : 0 < d) :
    ∃ n, q n < n ∧ n - q n = d := by
  -- Pass the thirty-column seed and leave room for all four retained diagonals.
  let k := d + 34
  have hcolumn : k ≤ lowerColumn k :=
    (lowerColumn_strictMono (infinite_lowerColumns q_surjective)).id_le k
  have hn : 30 ≤ lowerColumn k := by dsimp [k] at hcolumn ⊢; omega
  obtain ⟨s, hrep, hcert, _⟩ :=
    actualInvariant_of_localStepExact local_step_exact (lowerColumn k) hn
  have hbounds := hrep.toRecordsRepresented.diagonalRecordBounds
    (Finite.certified_condition hcert)
  have hcard : (diagonalOffsets (lowerColumn k)).card ≤ 4 := by
    have h := Finset.card_le_card hbounds.2
    simpa using h
  have hrank := nextLowerRank_eq_reference_add_offsets (lowerColumn k)
  rw [nextLowerRank_lowerColumn] at hrank
  have hk : k = d + 34 := rfl
  have href : d < diagonalReference (lowerColumn k) := by omega
  have hused := mem_lowerDiagonals_of_lt_reference hd href
  obtain ⟨n, hn, hdiag⟩ := Finset.mem_image.mp hused
  exact ⟨n, (Finset.mem_filter.mp hn).2, hdiag⟩

/-- **Corollary 18, coverage.** Every integer occurs as the signed diagonal
`q n - n` of some greedy queen. Zero is occupied by the queen at the origin. -/
theorem q_diagonal_surjective : Function.Surjective (fun n => (q n : ℤ) - (n : ℤ)) := by
  intro z
  cases z with
  | ofNat k =>
    by_cases hk : k = 0
    · subst k
      exact ⟨0, by simp⟩
    · obtain ⟨n, _, hdiag⟩ := exists_upper_diagonal k (by omega)
      exact ⟨n, hdiag⟩
  | negSucc k =>
    obtain ⟨n, hlower, hdiag⟩ := exists_lower_diagonal (k + 1) (by omega)
    refine ⟨n, ?_⟩
    change (q n : ℤ) - (n : ℤ) = Int.negSucc k
    omega

/-- **Corollary 18 (diagonal coverage).** The signed-diagonal map is a
bijection from natural column indices to all integers. -/
theorem q_diagonal_bijective : Function.Bijective (fun n => (q n : ℤ) - (n : ℤ)) :=
  ⟨q_diagonal_injective, q_diagonal_surjective⟩

/-- **Corollary 18**, expressed geometrically: every signed diagonal contains
exactly one queen of the greedy construction. -/
theorem existsUnique_queen_on_diagonal (z : ℤ) : ∃! n, (q n : ℤ) - (n : ℤ) = z :=
  q_diagonal_bijective.existsUnique z

/-- Chronological lower queens have distinct positive diagonal magnitudes,
the injectivity part of Corollary 18's final assertion. -/
theorem lowerDiagonal_injective : Function.Injective lowerDiagonal := by
  intro i j hij
  apply (lowerColumn_strictMono (infinite_lowerColumns q_surjective)).injective
  apply q_diagonal_injective
  have hi := lowerDiagonal_cast i
  have hj := lowerDiagonal_cast j
  have heq := congrArg (fun d : ℕ => (d : ℤ)) hij
  change (q (lowerColumn i) : ℤ) - (lowerColumn i : ℤ) =
    (q (lowerColumn j) : ℤ) - (lowerColumn j : ℤ)
  omega

/-- **Corollary 18, lower diagonals.** The chronological lower magnitudes
enumerate the positive integers bijectively. -/
theorem lowerDiagonal_bijOn : Set.BijOn lowerDiagonal Set.univ {d | 0 < d} := by
  refine ⟨?_, lowerDiagonal_injective.injOn, ?_⟩
  · intro k _
    have h := lowerColumn_lower (infinite_lowerColumns q_surjective) k
    change 0 < lowerColumn k - q (lowerColumn k)
    omega
  · intro d hd
    obtain ⟨n, hn, hdiag⟩ := exists_lower_diagonal d hd
    obtain ⟨k, hk⟩ := exists_lowerColumn_eq hn
    refine ⟨k, Set.mem_univ _, ?_⟩
    simpa only [lowerDiagonal, hk] using hdiag

end Queens
