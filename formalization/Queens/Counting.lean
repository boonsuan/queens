import Queens.GoldenRatio

/-!
# The counting recurrence

This file formalizes Lemma 7 of Section 3. Its hypotheses describe the
lower-column estimate, the fact that each column increments the upper
count by at most one, and the bracketing of a column by consecutive lower
columns. These facts must be supplied by the combinatorial construction.
-/

namespace Queens

/-- Lemma 7 in integer arithmetic. A column estimate at consecutive lower
columns bounds the recurrence defect. Keeping the calculation in `ℤ`
retains the one-unit improvement of a strict integer endpoint bound. -/
theorem counting_recurrence_int (U x : ℕ → ℕ) (C : ℕ)
    (hzero : U 0 = 0) (hbounded : ∀ n, U n ≤ n)
    (hstep : ∀ n, U (n + 1) ≤ U n + 1)
    (hleft : ∀ n, 0 < n - U n → x (n - U n) ≤ n)
    (hright : ∀ n, n < x (n - U n + 1))
    (hcolumns : ∀ j, 0 < j →
      |(x j : ℤ) - 2 * (j : ℤ) - (U (j - 1) : ℤ)| ≤ (C : ℤ))
    (n : ℕ) :
    |(n : ℤ) - 2 * (U n : ℤ) + (U (n - U n) : ℤ)| ≤ (C : ℤ) + 1 := by
  let j := n - U n
  have hsplit : n = U n + j := (Nat.add_sub_of_le (hbounded n)).symm
  have hnext := hright n
  change n < x (j + 1) at hnext
  have hupper := (abs_le.mp (hcolumns (j + 1) (by omega))).2
  simp only [Nat.add_sub_cancel] at hupper
  by_cases hj : j = 0
  · simp only [hj, Nat.cast_zero, zero_add, hzero] at hupper hnext
    change |(n : ℤ) - 2 * (U n : ℤ) + (U j : ℤ)| ≤ (C : ℤ) + 1
    rw [hj, hzero]
    apply abs_le.mpr
    constructor <;> omega
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hprevious := hleft n hjpos
    change x j ≤ n at hprevious
    have hlower := (abs_le.mp (hcolumns j hjpos)).1
    have hjpred : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
    have hstepj : U j ≤ U (j - 1) + 1 := by
      simpa only [hjpred] using hstep (j - 1)
    change |(n : ℤ) - 2 * (U n : ℤ) + (U j : ℤ)| ≤ (C : ℤ) + 1
    apply abs_le.mpr
    constructor <;> omega

/-- The real-valued formulation of Lemma 7, directly usable by
`count_error_lt`. All combinatorial assumptions remain explicit. -/
theorem counting_recurrence (U x : ℕ → ℕ) (C : ℕ)
    (hzero : U 0 = 0) (hbounded : ∀ n, U n ≤ n)
    (hstep : ∀ n, U (n + 1) ≤ U n + 1)
    (hleft : ∀ n, 0 < n - U n → x (n - U n) ≤ n)
    (hright : ∀ n, n < x (n - U n + 1))
    (hcolumns : ∀ j, 0 < j →
      |(x j : ℤ) - 2 * (j : ℤ) - (U (j - 1) : ℤ)| ≤ (C : ℤ))
    (n : ℕ) : |countDefect U n| ≤ (C : ℝ) + 1 := by
  unfold countDefect
  exact_mod_cast counting_recurrence_int U x C hzero hbounded hstep hleft hright hcolumns n

end Queens
