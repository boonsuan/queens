import Queens.LowerRuns

/-!
# Completeness of the lower-run enumeration

Corollary 19 describes both maximal lower-column intervals and their ordered
length sequence A275885. This file proves that the canonical enumeration in
`LowerRuns` lists every maximal lower run, exactly once. Thus the run-length
sequence used for A275887 has precisely the intended meaning.
-/

namespace Queens

/-- Every actual lower column belongs to one of the canonical lower runs.
The least endpoint after the column identifies the required run. -/
theorem exists_lowerRun_contains {n : ℕ} (hn : q n < n) :
    ∃ k, lowerRunStart k ≤ n ∧ n < lowerRunEnd k := by
  have hex : ∃ k, n < lowerRunEnd k := by
    refine ⟨n + 1, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self n) (lowerRunEnd_strictMono.id_le (n + 1))
  let k := Nat.find hex
  have hend : n < lowerRunEnd k := Nat.find_spec hex
  have hmin : ∀ j < k, lowerRunEnd j ≤ n := by
    intro j hj
    exact Nat.le_of_not_gt (Nat.find_min hex hj)
  refine ⟨k, ?_, hend⟩
  by_contra hstart
  have hu : IsUpperColumnWithOrigin n := by
    cases hk : k with
    | zero =>
      rw [hk] at hstart
      exact upper_before_first_run (by omega)
    | succ j =>
      rw [hk] at hstart hmin
      exact upper_between_runs (hmin j (Nat.lt_succ_self j)) (by omega)
  exact (not_upperColumnWithOrigin_iff n).mpr hn hu

/-- Distinct enumerated lower runs are disjoint and occur in increasing
order, with a nonempty upper block between them. -/
theorem lowerRunEnd_lt_start_of_lt {i j : ℕ} (hij : i < j) :
    lowerRunEnd i < lowerRunStart j :=
  (lowerRunEnd_lt_start_succ i).trans_le
    (lowerRunStart_strictMono.monotone (by omega))

/-- Every lower column belongs to exactly one enumerated run. -/
theorem existsUnique_lowerRun_contains {n : ℕ} (hn : q n < n) :
    ∃! k, lowerRunStart k ≤ n ∧ n < lowerRunEnd k := by
  obtain ⟨k, hk⟩ := exists_lowerRun_contains hn
  refine ⟨k, hk, ?_⟩
  intro j hj
  rcases lt_trichotomy j k with hlt | heq | hgt
  · have := lowerRunEnd_lt_start_of_lt hlt
    omega
  · exact heq
  · have := lowerRunEnd_lt_start_of_lt hgt
    omega

/-- **Corollary 19, enumeration correspondence.** Every maximal lower-column
run is one of the canonical intervals used to define A275885, and conversely. -/
theorem maximal_lower_run_iff {start length : ℕ} :
    Sequence.MaximalRun (fun n => q n < n) start length ↔
      ∃ k, start = lowerRunStart k ∧ length = lowerRunLength k := by
  constructor
  · intro h
    obtain ⟨k, hle, hlt⟩ := exists_lowerRun_contains h.first
    have heq : start = lowerRunStart k := by
      by_contra hne
      have hprev : q (start - 1) < start - 1 := lower_in_run (k := k) (by omega) (by omega)
      have hnot := h.2.2.1.resolve_left (by omega)
      exact hnot hprev
    refine ⟨k, heq, ?_⟩
    apply h.length_unique
    simpa only [heq] using lowerRun_maximal k
  · rintro ⟨k, rfl, rfl⟩
    exact lowerRun_maximal k

/-- The canonical indexing lists each maximal lower-column interval once.
This makes the use of its ordered lengths in A275887 unambiguous. -/
theorem existsUnique_lowerRun_of_maximal {start length : ℕ}
    (h : Sequence.MaximalRun (fun n => q n < n) start length) :
    ∃! k, start = lowerRunStart k ∧ length = lowerRunLength k := by
  obtain ⟨k, hk⟩ := maximal_lower_run_iff.mp h
  refine ⟨k, hk, ?_⟩
  intro j hj
  exact lowerRunStart_strictMono.injective (hj.1.symm.trans hk.1)

/-- **Corollary 19, A275885 in sequence form:** the range of the canonical
lower-run length sequence is exactly `{1, 2, 3}`. -/
theorem lowerRunLength_range (length : ℕ) :
    (∃ k, lowerRunLength k = length) ↔ length ∈ Finset.Icc 1 3 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact Finset.mem_Icc.mpr (lowerRunLength_bounds k)
  · intro h
    obtain ⟨start, hrun⟩ := (lower_column_run_lengths length).mpr h
    obtain ⟨k, _, hlength⟩ := maximal_lower_run_iff.mp hrun
    exact ⟨k, hlength.symm⟩

end Queens
