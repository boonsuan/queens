import Queens.Exactness
import Queens.Finite.RunBounds
import Queens.Finite.RunWitnesses

/-!
# The basic column runs and gaps of Corollary 19

This file proves the first, second, fourth, and fifth rows of Corollary 19.
Exclusion comes from the actual queen word following the twelve-symbol graph;
attainment comes from independently checked actual greedy queens. In keeping
with the paper and the OEIS entries, the origin is counted as an upper column.
-/

namespace Queens

/-- Corollary 19: upper-column membership with the origin included, as required
by A275886 and A275888. Away from zero this is the usual strict upper condition. -/
def IsUpperColumnWithOrigin (n : ℕ) : Prop := n = 0 ∨ n < q n

/-- Corollary 19: lower columns are exactly the complement of upper columns
when the origin is counted as upper. -/
theorem not_upperColumnWithOrigin_iff (n : ℕ) :
    ¬IsUpperColumnWithOrigin n ↔ q n < n := by
  unfold IsUpperColumnWithOrigin
  by_cases hn : n = 0
  · simp [hn]
  · have hne := q_ne_self (show 0 < n by omega)
    simp only [hn, false_or]
    omega

/-- Section 6.4 applied to an arbitrary positive starting column: every
consecutive twelve-symbol block of the actual word is a history vertex. -/
theorem queenWord_history_vertex {start : ℕ} (hstart : 0 < start) :
    Finite.encode (wordSegment start Finite.historyLength) ∈
      Finite.Data.historyGraph.map Prod.fst := by
  obtain ⟨_, _, _, hword⟩ := actualInvariant_of_localStepExact local_step_exact
    (start + 30) (by omega)
  have ht : start + 11 ∈ Finset.Icc Finite.historyLength (start + 30 - 1) := by
    simp only [Finset.mem_Icc, Finite.historyLength]
    omega
  have hv := (hword (start + 11) ht).1
  have heq : start + 11 + 1 - Finite.historyLength = start := by
    simp [Finite.historyLength]
  simpa only [Finite.historyWindow, heq, wordSegment] using hv

private theorem decoded_history_symbol (start : ℕ) {i : ℕ}
    (hi : i < Finite.historyLength) :
    (Finite.decode (Finite.encode (wordSegment start Finite.historyLength))
      Finite.historyLength)[i]?.getD 0 = queenSymbol (start + i) := by
  have hdecode : Finite.decode (Finite.encode (wordSegment start Finite.historyLength))
      Finite.historyLength = wordSegment start Finite.historyLength := by
    have hvalid : ∀ s ∈ wordSegment start Finite.historyLength, s < 4 := by
      intro s hs
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hs
      exact queenSymbol_lt_four _
    simpa using Finite.decode_encode hvalid
  rw [hdecode]
  simp [wordSegment, hi]

/-- Corollary 19: four consecutive lower columns never occur. The origin is
handled directly; every positive-index block lies in a certified history. -/
theorem no_four_lower_columns (start : ℕ) :
    ¬∀ i : Fin 4, q (start + i.val) < start + i.val := by
  intro h
  by_cases hs : start = 0
  · simpa [hs] using h 0
  · obtain ⟨i, hi⟩ := (Finite.historyGraph_run_bounds _
        (queenWord_history_vertex (by omega : 0 < start))).1
    have hib : i.val < Finite.historyLength := by
      dsimp [Finite.historyLength]
      omega
    rw [decoded_history_symbol start hib, upperBit_queenSymbol] at hi
    have hlower := h i
    have hnot : ¬ start + i.val < q (start + i.val) := by omega
    exact hi (by simp [columnBit, hnot])

/-- Corollary 19: six consecutive upper columns never occur, including a
possible run starting at the origin. -/
theorem no_six_upper_columns (start : ℕ) :
    ¬∀ i : Fin 6, IsUpperColumnWithOrigin (start + i.val) := by
  intro h
  by_cases hs : start = 0
  · have hthree := h 3
    have hq : q 3 = 1 := by rw [Finite.q_eq_seedRow (by decide)]; decide
    simp [hs, IsUpperColumnWithOrigin, hq] at hthree
  · obtain ⟨i, hi⟩ := (Finite.historyGraph_run_bounds _
        (queenWord_history_vertex (by omega : 0 < start))).2
    have hib : i.val < Finite.historyLength := by
      dsimp [Finite.historyLength]
      omega
    rw [decoded_history_symbol start hib, upperBit_queenSymbol] at hi
    have hupper : start + i.val < q (start + i.val) := (h i).resolve_left (by omega)
    exact hi (by simp [columnBit, hupper])

private theorem lower_witness_iff {n : ℕ} (hn : n < 5000) :
    Finite.runWitnessLower n ↔ q n < n := by
  rw [Finite.runWitnessLower, Finite.q_eq_runWitnessRow hn]

private theorem upper_witness_iff {n : ℕ} (hn : n < 5000) :
    Finite.runWitnessUpper n ↔ IsUpperColumnWithOrigin n := by
  rw [Finite.runWitnessUpper, IsUpperColumnWithOrigin, Finite.q_eq_runWitnessRow hn]

/-- **Corollary 19, A275885:** the lengths of maximal lower-column runs are
exactly 1, 2, and 3. Each permitted length is attained by actual greedy queens. -/
theorem lower_column_run_lengths (length : ℕ) :
    (∃ start, Sequence.MaximalRun (fun n => q n < n) start length) ↔
      length ∈ Finset.Icc 1 3 := by
  constructor
  · rintro ⟨start, h⟩
    exact Finset.mem_Icc.mpr ⟨h.1, h.length_le no_four_lower_columns⟩
  · intro h
    have hl := Finset.mem_Icc.mp h
    obtain ⟨hbound, hwitness⟩ := Finite.basicRunWitnesses_checked.1
      ⟨length, by omega⟩ hl.1
    dsimp only at hbound hwitness
    refine ⟨Finite.lowerRunWitnessStart length, ?_⟩
    exact (Sequence.maximalRun_congr (fun i hi => lower_witness_iff (by omega))).mp hwitness

/-- **Corollary 19, A275886:** counting the origin as upper, the lengths of
maximal upper-column runs are exactly 1 through 5. -/
theorem upper_column_run_lengths (length : ℕ) :
    (∃ start, Sequence.MaximalRun IsUpperColumnWithOrigin start length) ↔
      length ∈ Finset.Icc 1 5 := by
  constructor
  · rintro ⟨start, h⟩
    exact Finset.mem_Icc.mpr ⟨h.1, h.length_le no_six_upper_columns⟩
  · intro h
    have hl := Finset.mem_Icc.mp h
    obtain ⟨hbound, hwitness⟩ := Finite.basicRunWitnesses_checked.2.1
      ⟨length, by omega⟩ hl.1
    dsimp only at hbound hwitness
    refine ⟨Finite.upperRunWitnessStart length, ?_⟩
    exact (Sequence.maximalRun_congr (fun i hi => upper_witness_iff (by omega))).mp hwitness

/-- **Corollary 19, A275888:** counting the origin as upper, the gaps between
consecutive upper columns are exactly 1 through 4. -/
theorem upper_column_gaps (gap : ℕ) :
    (∃ start, Sequence.ConsecutiveGap IsUpperColumnWithOrigin start gap) ↔
      gap ∈ Finset.Icc 1 4 := by
  constructor
  · rintro ⟨start, h⟩
    refine Finset.mem_Icc.mpr ⟨h.1, h.length_le ?_⟩
    intro s hs
    apply no_four_lower_columns s
    intro i
    exact (not_upperColumnWithOrigin_iff _).mp (hs i)
  · intro h
    have hg := Finset.mem_Icc.mp h
    obtain ⟨hbound, hwitness⟩ := Finite.basicRunWitnesses_checked.2.2.1
      ⟨gap, by omega⟩ hg.1
    dsimp only at hbound hwitness
    refine ⟨Finite.upperGapWitnessStart gap, ?_⟩
    exact (Sequence.consecutiveGap_congr (fun i hi => upper_witness_iff (by omega))).mp hwitness

/-- **Corollary 19, A275889:** the gaps between consecutive lower columns are
exactly 1 through 6. -/
theorem lower_column_gaps (gap : ℕ) :
    (∃ start, Sequence.ConsecutiveGap (fun n => q n < n) start gap) ↔
      gap ∈ Finset.Icc 1 6 := by
  constructor
  · rintro ⟨start, h⟩
    refine Finset.mem_Icc.mpr ⟨h.1, h.length_le ?_⟩
    intro s hs
    apply no_six_upper_columns s
    intro i
    by_contra hu
    exact hs i ((not_upperColumnWithOrigin_iff _).mp hu)
  · intro h
    have hg := Finset.mem_Icc.mp h
    obtain ⟨hbound, hwitness⟩ := Finite.basicRunWitnesses_checked.2.2.2
      ⟨gap, by omega⟩ hg.1
    dsimp only at hbound hwitness
    refine ⟨Finite.lowerGapWitnessStart gap, ?_⟩
    exact (Sequence.consecutiveGap_congr (fun i hi => lower_witness_iff (by omega))).mp hwitness

end Queens
