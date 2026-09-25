import Queens.RunsAndGaps

/-!
# The sequence of lower-column run lengths

Corollary 19 calls this sequence `r` (OEIS A275885). Starting at column zero,
we repeatedly find the first lower column, then the next upper column. The
least-index definitions make the ordering and the intervening upper blocks
explicit; `lowerRun_maximal` proves that the resulting intervals are maximal.
-/

namespace Queens

private theorem exists_upper_near (n : ℕ) :
    ∃ k, n ≤ k ∧ k ≤ n + 3 ∧ IsUpperColumnWithOrigin k := by
  classical
  by_contra h
  push Not at h
  apply no_four_lower_columns n
  intro i
  apply (not_upperColumnWithOrigin_iff _).mp
  exact h _ (by omega) (by have := i.isLt; omega)

private theorem exists_lower_near (n : ℕ) :
    ∃ k, n ≤ k ∧ k ≤ n + 5 ∧ q k < k := by
  classical
  by_contra h
  push Not at h
  apply no_six_upper_columns n
  intro i
  by_contra hu
  have hge := h (n + i.val) (by omega) (by have := i.isLt; omega)
  have hlt := (not_upperColumnWithOrigin_iff _).mp hu
  omega

private theorem exists_upper_from (n : ℕ) : ∃ k, n ≤ k ∧ IsUpperColumnWithOrigin k := by
  obtain ⟨k, hkn, _, hk⟩ := exists_upper_near n
  exact ⟨k, hkn, hk⟩

private theorem exists_lower_from (n : ℕ) : ∃ k, n ≤ k ∧ q k < k := by
  obtain ⟨k, hkn, _, hk⟩ := exists_lower_near n
  exact ⟨k, hkn, hk⟩

/-- Corollary 19: the first upper column at or after `n`, counting the origin
as upper. Its existence follows from the bound on lower-column runs. -/
noncomputable def nextUpperColumn (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_upper_from n)

/-- Corollary 19: the first lower column at or after `n`. Its existence follows
from the bound on upper-column runs. -/
noncomputable def nextLowerColumn (n : ℕ) : ℕ := Nat.find (exists_lower_from n)

/-- For Corollary 19, the first upper column lies at or after the requested column. -/
theorem le_nextUpperColumn (n : ℕ) : n ≤ nextUpperColumn n := by
  classical
  exact (Nat.find_spec (exists_upper_from n)).1

/-- For Corollary 19, the first upper column has the requested upper classification. -/
theorem nextUpperColumn_upper (n : ℕ) : IsUpperColumnWithOrigin (nextUpperColumn n) := by
  classical
  exact (Nat.find_spec (exists_upper_from n)).2

/-- For Corollary 19, the first lower column lies at or after the requested column. -/
theorem le_nextLowerColumn (n : ℕ) : n ≤ nextLowerColumn n :=
  (Nat.find_spec (exists_lower_from n)).1

/-- For Corollary 19, the first lower column has the requested lower classification. -/
theorem nextLowerColumn_lower (n : ℕ) : q (nextLowerColumn n) < nextLowerColumn n :=
  (Nat.find_spec (exists_lower_from n)).2

/-- For Corollary 19, minimality of the next upper column. -/
theorem nextUpperColumn_le {n k : ℕ} (hn : n ≤ k) (hk : IsUpperColumnWithOrigin k) :
    nextUpperColumn n ≤ k := by
  classical
  exact Nat.find_min' (exists_upper_from n) ⟨hn, hk⟩

/-- For Corollary 19, minimality of the next lower column. -/
theorem nextLowerColumn_le {n k : ℕ} (hn : n ≤ k) (hk : q k < k) :
    nextLowerColumn n ≤ k := Nat.find_min' (exists_lower_from n) ⟨hn, hk⟩

/-- For Corollary 19, the columns before the next upper column are lower. -/
theorem lower_before_nextUpperColumn {n k : ℕ} (hn : n ≤ k)
    (hk : k < nextUpperColumn n) : q k < k := by
  apply (not_upperColumnWithOrigin_iff _).mp
  intro hu
  have := nextUpperColumn_le hn hu
  omega

/-- For Corollary 19, the columns before the next lower column are upper. -/
theorem upper_before_nextLowerColumn {n k : ℕ} (hn : n ≤ k)
    (hk : k < nextLowerColumn n) : IsUpperColumnWithOrigin k := by
  by_contra hu
  have := nextLowerColumn_le hn ((not_upperColumnWithOrigin_iff _).mp hu)
  omega

/-- Corollary 19: the next upper column occurs within three columns. -/
theorem nextUpperColumn_le_add_three (n : ℕ) : nextUpperColumn n ≤ n + 3 := by
  obtain ⟨k, hkn, hkbound, hk⟩ := exists_upper_near n
  exact (nextUpperColumn_le hkn hk).trans hkbound

/-- Corollary 19: the next lower column occurs within five columns. -/
theorem nextLowerColumn_le_add_five (n : ℕ) : nextLowerColumn n ≤ n + 5 := by
  obtain ⟨k, hkn, hkbound, hk⟩ := exists_lower_near n
  exact (nextLowerColumn_le hkn hk).trans hkbound

/-- Corollary 19, A275885: the starting columns of successive lower runs,
indexed from zero. Each next search begins at the preceding upper endpoint. -/
noncomputable def lowerRunStart : ℕ → ℕ
  | 0 => nextLowerColumn 0
  | k + 1 => nextLowerColumn (nextUpperColumn (lowerRunStart k))

/-- Corollary 19, A275885: the upper column immediately after the `k`th lower
run. The lower run occupies the half-open interval from start to end. -/
noncomputable def lowerRunEnd (k : ℕ) : ℕ := nextUpperColumn (lowerRunStart k)

/-- Corollary 19, A275885: the infinite sequence of lower-column run lengths. -/
noncomputable def lowerRunLength (k : ℕ) : ℕ := lowerRunEnd k - lowerRunStart k

/-- For Corollary 19, every lower-run start is a lower column. -/
theorem lowerRunStart_lower (k : ℕ) : q (lowerRunStart k) < lowerRunStart k := by
  cases k <;> exact nextLowerColumn_lower _

/-- For Corollary 19, every lower-run endpoint is an upper column. -/
theorem lowerRunEnd_upper (k : ℕ) : IsUpperColumnWithOrigin (lowerRunEnd k) :=
  nextUpperColumn_upper _

/-- For Corollary 19, every enumerated lower run is nonempty. -/
theorem lowerRunStart_lt_end (k : ℕ) : lowerRunStart k < lowerRunEnd k := by
  have hle := le_nextUpperColumn (lowerRunStart k)
  change lowerRunStart k ≤ lowerRunEnd k at hle
  have hlow := lowerRunStart_lower k
  have hu := lowerRunEnd_upper k
  have hnot := (not_upperColumnWithOrigin_iff _).mpr hlow
  by_contra h
  have : lowerRunEnd k = lowerRunStart k := by omega
  exact hnot (this ▸ hu)

/-- Corollary 19: adding a lower run's length to its start gives the first
following upper column. This is the endpoint identity used in path contraction. -/
@[simp] theorem lowerRunStart_add_length (k : ℕ) :
    lowerRunStart k + lowerRunLength k = lowerRunEnd k :=
  Nat.add_sub_of_le (lowerRunStart_lt_end k).le

/-- For Corollary 19, the upper block between consecutive lower runs is nonempty. -/
theorem lowerRunEnd_lt_start_succ (k : ℕ) : lowerRunEnd k < lowerRunStart (k + 1) := by
  have hle := le_nextLowerColumn (lowerRunEnd k)
  have hu := lowerRunEnd_upper k
  have hnot := (not_upperColumnWithOrigin_iff _).mpr (lowerRunStart_lower (k + 1))
  change lowerRunEnd k < nextLowerColumn (lowerRunEnd k)
  by_contra h
  have heq : lowerRunStart (k + 1) = lowerRunEnd k := by
    change nextLowerColumn (lowerRunEnd k) = lowerRunEnd k
    omega
  exact hnot (heq ▸ hu)

/-- For Corollary 19, the canonical run starts are strictly increasing. -/
theorem lowerRunStart_strictMono : StrictMono lowerRunStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact (lowerRunStart_lt_end k).trans (lowerRunEnd_lt_start_succ k)

/-- For Corollary 19, the canonical run endpoints are strictly increasing. -/
theorem lowerRunEnd_strictMono : StrictMono lowerRunEnd := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact (lowerRunEnd_lt_start_succ k).trans (lowerRunStart_lt_end (k + 1))

/-- Corollary 19: every term of A275885 is between one and three. -/
theorem lowerRunLength_bounds (k : ℕ) : 1 ≤ lowerRunLength k ∧ lowerRunLength k ≤ 3 := by
  have hpos := lowerRunStart_lt_end k
  have hbound := nextUpperColumn_le_add_three (lowerRunStart k)
  change lowerRunEnd k ≤ lowerRunStart k + 3 at hbound
  unfold lowerRunLength
  omega

/-- For Corollary 19, the columns in an enumerated lower run are lower. -/
theorem lower_in_run {k n : ℕ} (hstart : lowerRunStart k ≤ n) (hend : n < lowerRunEnd k) :
    q n < n := lower_before_nextUpperColumn hstart hend

/-- For Corollary 19, between consecutive lower runs all columns are upper. -/
theorem upper_between_runs {k n : ℕ} (hend : lowerRunEnd k ≤ n)
    (hstart : n < lowerRunStart (k + 1)) : IsUpperColumnWithOrigin n :=
  upper_before_nextLowerColumn hend hstart

/-- Corollary 19: the initial columns before the first lower run are upper. -/
theorem upper_before_first_run {n : ℕ} (hn : n < lowerRunStart 0) :
    IsUpperColumnWithOrigin n := upper_before_nextLowerColumn (Nat.zero_le _) hn

/-- Corollary 19: each interval in the canonical enumeration is a maximal
lower-column run, with the correct left and right boundary conditions. -/
theorem lowerRun_maximal (k : ℕ) :
    Sequence.MaximalRun (fun n => q n < n) (lowerRunStart k) (lowerRunLength k) := by
  refine ⟨(lowerRunLength_bounds k).1, ?_, ?_, ?_⟩
  · intro i
    exact lower_in_run (Nat.le_add_right _ _)
      (by simpa using Nat.add_lt_add_left i.isLt (lowerRunStart k))
  · right
    have hstartpos : 0 < lowerRunStart k := by have := lowerRunStart_lower k; omega
    have hu : IsUpperColumnWithOrigin (lowerRunStart k - 1) := by
      cases k with
      | zero => exact upper_before_first_run (by omega)
      | succ k =>
        have hg := lowerRunEnd_lt_start_succ k
        exact upper_between_runs (k := k) (by omega) (by omega)
    intro hl
    exact (not_upperColumnWithOrigin_iff _).mpr hl hu
  · rw [lowerRunStart_add_length]
    intro hl
    exact (not_upperColumnWithOrigin_iff _).mpr hl (lowerRunEnd_upper k)

end Queens
