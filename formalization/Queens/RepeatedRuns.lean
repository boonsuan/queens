import Queens.FortyPath
import Queens.Finite.RepeatedRunCertificate
import Queens.Finite.LowerRunWitnesses

/-!
# Runs of equal lower-run lengths: the third row of Corollary 19

The canonical sequence `lowerRunLength` is A275885. We contract the actual
forty-symbol state path at the upper endpoints of successive lower runs, obtaining
a labeled walk whose labels are the successive terms of that sequence. The
checked remaining-length certificate bounds every later maximal repetition.
Checked actual-prefix intervals handle the early repetitions and attainment.
-/

namespace Queens

private theorem actualFortyPath : Finite.fortyRunAdjacency.IsPath
    (fun j => (Finite.Forty.actualVertex j).val) := by
  intro j
  rw [Finite.fortyRunAdjacency_eq (Finite.Forty.actualVertex j).isLt]
  exact Finite.Forty.actualVertex_step j

private theorem actualFortyUpper_iff (j : ℕ) :
    Finite.fortyStateUpper (Finite.Forty.actualVertex j).val = true ↔
      IsUpperColumnWithOrigin (79 + j) := by
  rw [Finite.fortyStateUpper_eq (Finite.Forty.actualVertex j).isLt]
  change decide (Finite.upperBit
    ((Finite.Forty.state (Finite.Forty.actualVertex j)).output % 4) = 1) = true ↔
      IsUpperColumnWithOrigin (79 + j)
  rw [Finite.Forty.actualVertex_output]
  simp [columnBit, IsUpperColumnWithOrigin]

/-- Appendix A: consecutive actual lower runs give a run-graph edge whenever
the first upper endpoint is covered by the forty-symbol state path. -/
theorem lowerRuns_fortyRunEdge {k : ℕ} (hk : 79 ≤ lowerRunEnd k) :
    Finite.FortyRunEdge
      (Finite.Forty.actualVertex (lowerRunEnd k - 79)).val
      (lowerRunLength (k + 1))
      (Finite.Forty.actualVertex (lowerRunEnd (k + 1) - 79)).val := by
  have hgap := lowerRunEnd_lt_start_succ k
  have hlen := lowerRunLength_bounds (k + 1)
  have hgapBound := nextLowerColumn_le_add_five (lowerRunEnd k)
  change lowerRunStart (k + 1) ≤ lowerRunEnd k + 5 at hgapBound
  have hend := lowerRunStart_lt_end (k + 1)
  have hjoin := lowerRunStart_add_length (k + 1)
  have hindex : lowerRunEnd k - 79 + (lowerRunStart (k + 1) - lowerRunEnd k) +
      lowerRunLength (k + 1) = lowerRunEnd (k + 1) - 79 := by omega
  refine ⟨Finite.repeatedRunTree_lookup_exists (Finite.Forty.actualVertex _).isLt, ?_, ?_⟩
  · apply (actualFortyUpper_iff _).mpr
    simpa only [show 79 + (lowerRunEnd k - 79) = lowerRunEnd k by omega] using lowerRunEnd_upper k
  · have h := Finite.runTargets_mem (upper := Finite.fortyStateUpper) actualFortyPath
      (fuel := 5) (start := lowerRunEnd k - 79)
      (distance := lowerRunStart (k + 1) - lowerRunEnd k)
      (length := lowerRunLength (k + 1)) (by omega) (by omega) hlen.1 hlen.2
    rw [hindex] at h
    apply h
    · intro i hi
      apply (actualFortyUpper_iff _).mpr
      have hi' := i.isLt
      have hcol : 79 + (lowerRunEnd k - 79 + i.val) = lowerRunEnd k + i.val := by omega
      rw [hcol]
      exact upper_between_runs (k := k) (by omega) (by omega)
    · intro i
      apply Bool.eq_false_iff.mpr
      intro hu
      have hu' := (actualFortyUpper_iff _).mp hu
      have hi := i.isLt
      have hcol : 79 + (lowerRunEnd k - 79 +
          (lowerRunStart (k + 1) - lowerRunEnd k) + i.val) =
            lowerRunStart (k + 1) + i.val := by omega
      rw [hcol] at hu'
      have hl := lower_in_run (k := k + 1) (n := lowerRunStart (k + 1) + i.val)
        (by omega) (by omega)
      exact (not_upperColumnWithOrigin_iff _).mpr hl hu'
    · apply (actualFortyUpper_iff _).mpr
      simpa only [show 79 + (lowerRunEnd (k + 1) - 79) = lowerRunEnd (k + 1) by omega] using
        lowerRunEnd_upper (k + 1)

/-- Appendix A: the A275885 terms beginning with term 24 (zero-based index 23)
are the labels of an actual walk in the certified run graph. -/
theorem lowerRunLength_follows_runGraph : Sequence.LabeledWalk Finite.FortyRunEdge
    (fun j => (Finite.Forty.actualVertex (lowerRunEnd (22 + j) - 79)).val)
    (fun j => lowerRunLength (23 + j)) := by
  intro j
  have hm := lowerRunEnd_strictMono.monotone (show 22 ≤ 22 + j by omega)
  rw [Finite.lowerRunEnd_twentyTwo] at hm
  have h := lowerRuns_fortyRunEdge (k := 22 + j) (by omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem runGraphVertex_upper (j : ℕ) :
    Finite.fortyStateUpper (Finite.Forty.actualVertex (lowerRunEnd (22 + j) - 79)).val = true := by
  have hm := lowerRunEnd_strictMono.monotone (show 22 ≤ 22 + j by omega)
  rw [Finite.lowerRunEnd_twentyTwo] at hm
  apply (actualFortyUpper_iff _).mpr
  simpa only [show 79 + (lowerRunEnd (22 + j) - 79) = lowerRunEnd (22 + j) by omega] using
    lowerRunEnd_upper (22 + j)

/-- Corollary 19: twelve consecutive terms of A275885 cannot all be equal.
This excludes infinite constant tails as well as overly long finite repetitions. -/
theorem no_twelve_equal_lower_run_lengths (start c : ℕ) :
    ¬∀ i : Fin 12, lowerRunLength (start + i.val) = c := by
  intro h
  have hfirst := h 0
  simp only [Fin.val_zero, Nat.add_zero] at hfirst
  have hc := lowerRunLength_bounds start
  rw [hfirst] at hc
  by_cases hs : start < 23
  · apply Finite.earlyNoTwelve_checked ⟨start, hs⟩ ⟨c, by omega⟩
    intro i
    dsimp only
    rw [← Finite.lowerRunLength_eq_witness (by have := i.isLt; omega)]
    exact h i
  · have hcmem : c ∈ ({1, 2, 3} : Finset ℕ) := by simp; omega
    have hblock : ∀ i : Fin 12, lowerRunLength (23 + (start - 23 + i.val)) = c := by
      intro i
      have heq : 23 + (start - 23 + i.val) = start + i.val := by omega
      simpa only [heq] using h i
    have hpath := lowerRunLength_follows_runGraph.constantLabelPath hblock
    have hbound := Finite.repeatedRunCertificate.constantPath_length_le hcmem hpath
      (Finite.repeatedRunLengths_nonempty
        (Finite.repeatedRunTree_lookup_exists (Finite.Forty.actualVertex _).isLt)
        (runGraphVertex_upper (start - 23 + 12)) hcmem)
      (fun k hk => Finite.repeatedRunLengths_le_eleven
        (Finite.repeatedRunTree_lookup_exists (Finite.Forty.actualVertex _).isLt)
        (runGraphVertex_upper (start - 23)) hcmem hk)
    omega

/-- Corollary 19: maximal repetitions whose start precedes the graph's safe
left boundary have an allowed length, by the checked actual-prefix table. -/
theorem early_repeated_lower_run_length {start length c : ℕ}
    (hs : start < 24)
    (h : Sequence.MaximalRun (fun k => lowerRunLength k = c) start length) :
    Finite.AllowedRepeatedRunLength length := by
  have hc : 1 ≤ c ∧ c ≤ 3 := h.first ▸ lowerRunLength_bounds start
  have hfinitefirst : Finite.witnessLowerRunLength start = c := by
    rw [← Finite.lowerRunLength_eq_witness (by omega)]
    exact h.first
  have hfiniteleft : start = 0 ∨ Finite.witnessLowerRunLength (start - 1) ≠ c := by
    rw [← Finite.lowerRunLength_eq_witness (by omega)]
    exact h.2.2.1
  obtain ⟨l, hlpos, hlten, hlbound, hlrun⟩ := Finite.earlyRepeatedRuns_checked
    ⟨start, hs⟩ ⟨c, by omega⟩ hfinitefirst hfiniteleft
  dsimp only at hlpos hlten hlbound hlrun
  have hactual : Sequence.MaximalRun (fun k => lowerRunLength k = c) start l.val := by
    apply (Sequence.maximalRun_congr (fun i hi => ?_)).mp hlrun
    rw [Finite.lowerRunLength_eq_witness (by omega)]
  have heq := h.length_unique hactual
  have hll := l.isLt
  unfold Finite.AllowedRepeatedRunLength
  omega

/-- Corollary 19: every maximal run of equal lower-run lengths belongs to
`{1,…,9,11}`. In particular a maximal run of exactly ten equal terms is impossible. -/
theorem repeated_lower_run_length_bound {start length c : ℕ}
    (h : Sequence.MaximalRun (fun k => lowerRunLength k = c) start length) :
    Finite.AllowedRepeatedRunLength length := by
  by_cases hs : start < 24
  · exact early_repeated_lower_run_length hs h
  · have hc := lowerRunLength_bounds start
    have hfirst := h.first
    rw [hfirst] at hc
    have hcmem : c ∈ ({1, 2, 3} : Finset ℕ) := by simp; omega
    exact Finite.repeatedRunCertificate.maximalRun_length_mem
      lowerRunLength_follows_runGraph hcmem (by omega : 0 < start - 23)
      (h.shift (by omega : 23 ≤ start))

/-- **Corollary 19, A275887:** the lengths of maximal runs of equal terms in
the lower-column run sequence are exactly `{1,…,9,11}`. -/
theorem repeated_lower_run_lengths (length : ℕ) :
    (∃ c start, Sequence.MaximalRun (fun k => lowerRunLength k = c) start length) ↔
      Finite.AllowedRepeatedRunLength length := by
  constructor
  · rintro ⟨c, start, h⟩
    exact repeated_lower_run_length_bound h
  · rintro ⟨hpos, hbound, hten⟩
    obtain ⟨hlimit, hrun⟩ := Finite.repeatedRunWitnesses_checked ⟨length, by omega⟩ hpos hten
    dsimp only at hlimit hrun
    refine ⟨Finite.repeatedRunWitnessLabel length, Finite.repeatedRunWitnessStart length, ?_⟩
    apply (Sequence.maximalRun_congr (fun i hi => ?_)).mp hrun
    rw [Finite.lowerRunLength_eq_witness (by omega)]

/-- **Corollary 19:** ten never occurs as the length of a maximal run of equal
terms in A275885, although eleven does occur. -/
theorem no_ten_repeated_lower_runs (c start : ℕ) :
    ¬Sequence.MaximalRun (fun k => lowerRunLength k = c) start 10 := by
  intro h
  exact (repeated_lower_run_length_bound h).2.2 rfl

end Queens
