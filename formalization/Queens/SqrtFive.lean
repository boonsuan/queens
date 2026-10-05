import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Exact comparisons in `ℤ[√5]`

Section 6.6 computes the window bounds exactly in `ℚ(√5)`, and Theorem 2 has
constants such as `(19√5 - 49) / 8`. After multiplying by 8 or 16, every number
compared in the finite verification lies in `ℤ[√5]`. Mathlib's order on `ℤ√5`
is decidable by integer arithmetic, so these comparisons reduce in the Lean
kernel. This file evaluates `ℤ√5` in `ℝ`, proves that evaluation is monotone and
injective, and records the golden-ratio identities used to clear denominators.

## Main statements

* `Queens.sqrtFiveEval_le`: a comparison in `ℤ√5` gives the real comparison.
* `Queens.sqrtFiveEval_injective`: distinct elements of `ℤ√5` have distinct
  real values, since `√5` is irrational.
-/

namespace Queens

open scoped goldenRatio

/-- The ring `ℤ[√5]` with mathlib's order, which is decidable by integer
arithmetic. Section 6.6 scales its window bounds into this ring. -/
abbrev ZSqrtFive := ℤ√((5 : ℕ) : ℤ)

/-- Evaluation of `a + b√5 ∈ ℤ[√5]` as the real number `a + b * Real.sqrt 5`. -/
noncomputable def sqrtFiveEval : ZSqrtFive →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 5, by norm_num⟩

/-- The value of `a + b√5` is `a + b * Real.sqrt 5`. -/
@[simp] theorem sqrtFiveEval_apply (x : ZSqrtFive) :
    sqrtFiveEval x = x.re + x.im * Real.sqrt 5 := by
  simp [sqrtFiveEval]

/-- A nonnegative element of `ℤ√5` has a nonnegative real value. The four cases
of `Zsqrtd.Nonneg` compare `|a|` with `|b|√5` through their squares. -/
theorem sqrtFiveEval_nonneg {x : ZSqrtFive} (hx : 0 ≤ x) : 0 ≤ sqrtFiveEval x := by
  have hn : x.Nonneg := Zsqrtd.nonneg_iff_zero_le.mpr hx
  obtain ⟨a, b⟩ := x
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [sqrtFiveEval_apply]
  simp only [Zsqrtd.Nonneg, Zsqrtd.Nonnegg] at hn
  rcases a with a | a <;> rcases b with b | b <;> simp only [Zsqrtd.SqLe] at hn
  all_goals simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  · positivity
  · have hsquares : (5 * (b + 1) * (b + 1) : ℝ) ≤ a * a := by
      exact_mod_cast (by simpa using hn)
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (b + 1)) hs]
  · have hsquares : ((a + 1) * (a + 1) : ℝ) ≤ 5 * b * b := by
      exact_mod_cast (by simpa using hn)
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) b) hs]

/-- Evaluation in `ℝ` is monotone, so every comparison checked in `ℤ√5` is a
comparison of real numbers. -/
theorem sqrtFiveEval_le {x y : ZSqrtFive} (h : x ≤ y) : sqrtFiveEval x ≤ sqrtFiveEval y := by
  have hnonneg := sqrtFiveEval_nonneg (sub_nonneg.mpr h)
  rw [map_sub] at hnonneg
  linarith

/-- Evaluation in `ℝ` is injective, because `√5` is irrational. This gives the
strict inequalities of Theorem 2. -/
theorem sqrtFiveEval_injective : Function.Injective sqrtFiveEval := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ h
  rw [sqrtFiveEval_apply] at h
  have hb : b = 0 := by
    by_contra hb
    have hsqrt : Real.sqrt 5 = ((-a / b : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact Nat.prime_five.irrational_sqrt ⟨_, hsqrt.symm⟩
  subst hb
  have ha : a = 0 := by exact_mod_cast (by simpa using h)
  subst ha
  rfl

/-- The golden ratio in terms of `Real.sqrt 5`; this is mathlib's definition. -/
theorem goldenRatio_eq : φ = (1 + Real.sqrt 5) / 2 := rfl

/-- The inverse golden ratio is `(√5 - 1) / 2`, so `2 / φ` lies in `ℤ[√5]`. -/
theorem inv_goldenRatio_eq : φ⁻¹ = (Real.sqrt 5 - 1) / 2 := by
  rw [Real.inv_goldenRatio, Real.goldenConj]
  ring

end Queens
