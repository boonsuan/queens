import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting recurrences and golden-ratio bounds

This file formalizes the analytic parts of Proposition 8 (Section 3) and
Proposition 21 (Section 6.6). The recurrences and the identities relating
counts to queen positions are explicit hypotheses, so these results apply
independently of the greedy construction and its finite certificates.
-/

namespace Queens

open scoped goldenRatio

/-- The error of an upper-queen count from its expected slope, as in
Section 3, Proposition 8. -/
noncomputable def countError (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  (U n : ℝ) - φ⁻¹ * (n : ℝ)

/-- The integer recurrence's defect, viewed in the reals to avoid truncated
subtraction. This is `ηₙ` in Section 3. -/
noncomputable def countDefect (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) - 2 * (U n : ℝ) + (U (n - U n) : ℝ)

/-- The fixed-point identity used by the contraction arguments in
Propositions 8 and 21: adding one to the inverse golden ratio gives `φ`. -/
theorem goldenRatio_inv_add_one : φ⁻¹ + 1 = φ := by
  rw [Real.inv_goldenRatio, add_comm, ← sub_eq_add_neg, Real.one_sub_goldenRatio]

private lemma inv_phi_sq : (φ⁻¹) ^ 2 = 1 - φ⁻¹ := by
  rw [Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]
  ring

/-- Cancellation of the linear terms in the counting recurrence, the
algebraic identity behind the contraction in Proposition 8. -/
theorem countDefect_eq_error (U : ℕ → ℕ) (n : ℕ) (hbounded : U n ≤ n) :
    countDefect U n =
      countError U (n - U n) - (2 + φ⁻¹) * countError U n := by
  calc
    countDefect U n =
        countError U (n - U n) - (2 + φ⁻¹) * countError U n +
          (1 - φ⁻¹ - (φ⁻¹) ^ 2) * (n : ℝ) := by
      simp only [countDefect, countError, Nat.cast_sub hbounded]
      ring
    _ = _ := by rw [inv_phi_sq]; ring

/-- Proposition 8's count estimate, conditional on the counting recurrence.
The positive-count hypothesis ensures that `n - U n` is a smaller argument,
so strong induction implements the paper's contracting iteration. -/
theorem count_error_lt (U : ℕ → ℕ) (C : ℕ)
    (hzero : U 0 = 0) (hbounded : ∀ n, U n ≤ n)
    (hpositive : ∀ n, 0 < n → 0 < U n)
    (hrec : ∀ n, |countDefect U n| ≤ (C : ℝ) + 1) (n : ℕ) :
    |countError U n| < φ⁻¹ * ((C : ℝ) + 1) := by
  have hinv : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hC : 0 < (C : ℝ) + 1 := by positivity
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa [countError, hzero] using mul_pos hinv hC
    · have hsmaller : n - U n < n :=
        Nat.sub_lt (Nat.pos_of_ne_zero hn) (hpositive n (Nat.pos_of_ne_zero hn))
      have hprev := ih (n - U n) hsmaller
      have htriangle : (2 + φ⁻¹) * |countError U n| ≤
          |countError U (n - U n)| + ((C : ℝ) + 1) := by
        calc
          (2 + φ⁻¹) * |countError U n| =
              |countError U (n - U n) - countDefect U n| := by
            rw [countDefect_eq_error U n (hbounded n)]
            have hcoef : 0 ≤ 2 + φ⁻¹ := by positivity
            rw [sub_sub_cancel, abs_mul, abs_of_nonneg hcoef]
          _ ≤ |countError U (n - U n)| + |countDefect U n| := abs_sub _ _
          _ ≤ _ := add_le_add_right (hrec n) _
      have hfixed : (2 + φ⁻¹) * (φ⁻¹ * ((C : ℝ) + 1)) =
          φ⁻¹ * ((C : ℝ) + 1) + ((C : ℝ) + 1) := by
        have hsq := inv_phi_sq
        nlinarith [congrArg (fun x : ℝ => x * ((C : ℝ) + 1)) hsq]
      have hcontract : (2 + φ⁻¹) * |countError U n| <
          (2 + φ⁻¹) * (φ⁻¹ * ((C : ℝ) + 1)) := by
        rw [hfixed]
        exact htriangle.trans_lt (add_lt_add_left hprev _)
      exact (mul_lt_mul_iff_right₀ (by positivity : 0 < 2 + φ⁻¹)).mp hcontract

/-- Sections 3 and 6.6: the upper-row identity identifies position error
with count error. This algebraic step is shared by Propositions 8 and 21. -/
theorem upper_position_error_eq (U : ℕ → ℕ) (q n : ℕ)
    (hupper : q = n + U n) :
    (q : ℝ) - (n : ℝ) * φ = countError U n := by
  simp only [hupper, Nat.cast_add, countError]
  nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) goldenRatio_inv_add_one]

/-- Sections 3 and 6.6: splitting the lower-position error at the upper
count separates the combinatorial row discrepancy from the analytic count error. -/
theorem lower_position_error_eq (U : ℕ → ℕ) (q n : ℕ) :
    (q : ℝ) - (n : ℝ) / φ = (q : ℝ) - (U n : ℝ) + countError U n := by
  simp only [countError, div_eq_mul_inv]
  ring

/-- The upper-position conclusion of Proposition 8, from the upper-row
identity and an upper-count error bound. -/
theorem upper_position_error_lt (U : ℕ → ℕ) (q n : ℕ) (B : ℝ)
    (hupper : q = n + U n) (hcount : |countError U n| < B) :
    |(q : ℝ) - (n : ℝ) * φ| < B := by
  rwa [upper_position_error_eq U q n hupper]

/-- The lower-position conclusion of Proposition 8. The diagonal discrepancy
gives `|q - U n| ≤ C`; adding the count error gives the stated row error. -/
theorem lower_position_error_lt (U : ℕ → ℕ) (q n : ℕ) (C B : ℝ)
    (hlower : |(q : ℝ) - (U n : ℝ)| ≤ C)
    (hcount : |countError U n| < B) :
    |(q : ℝ) - (n : ℝ) / φ| < C + B := by
  calc
    |(q : ℝ) - (n : ℝ) / φ| =
        |((q : ℝ) - (U n : ℝ)) + countError U n| :=
      congrArg abs (lower_position_error_eq U q n)
    _ ≤ |(q : ℝ) - (U n : ℝ)| + |countError U n| := abs_add_le _ _
    _ < C + B := add_lt_add_of_le_of_lt hlower hcount

/-- Proposition 21's asymmetric contraction. The term at a strictly smaller
index lies in the same open interval, while the local contribution lies in
the closed interval `[-4, 1]`. A finite prefix supplies the initial bounds;
the paper takes `start = 30`. No finite-state assumptions enter this lemma. -/
theorem sharp_error_bounds_of_recursion (E : ℕ → ℝ) {start : ℕ}
    (hprefix : ∀ n < start, -3 / φ < E n ∧ E n < 2 / φ)
    (hrec : ∀ n, start ≤ n → ∃ t < n, ∃ a : ℝ,
      -4 ≤ a ∧ a ≤ 1 ∧ φ ^ 2 * E n = a + 1 + E t)
    (n : ℕ) : -3 / φ < E n ∧ E n < 2 / φ := by
  have hp := Real.goldenRatio_pos
  have hsq : 0 < φ ^ 2 := pow_pos hp _
  have hfixed (c : ℝ) : φ ^ 2 * (c / φ) = c + c / φ := by
    rw [div_eq_mul_inv]
    have hinv := goldenRatio_inv_add_one
    have hmul : φ * φ⁻¹ = 1 := mul_inv_cancel₀ Real.goldenRatio_ne_zero
    calc
      φ ^ 2 * (c * φ⁻¹) = c * φ * (φ * φ⁻¹) := by ring
      _ = c * φ := by rw [hmul, mul_one]
      _ = c + c * φ⁻¹ := by nlinarith [congrArg (fun x : ℝ => c * x) hinv]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < start
    · exact hprefix n hn
    · obtain ⟨t, ht, a, ha, ha', heq⟩ := hrec n (by omega)
      obtain ⟨hl, hu⟩ := ih t ht
      constructor
      · apply (mul_lt_mul_iff_right₀ hsq).mp
        rw [hfixed, heq]
        linarith
      · apply (mul_lt_mul_iff_right₀ hsq).mp
        rw [hfixed, heq]
        linarith

end Queens
