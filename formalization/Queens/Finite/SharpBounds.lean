import Queens.Finite.SharpChunks
import Queens.GoldenRatio

/-!
# Soundness of the sharper finite bounds

Proposition 21 uses integer inequalities checked in bounded kernel reductions.
This file extracts them from the invariant and derives the stated real bounds
using a proved rational enclosure of the golden ratio.
-/

namespace Queens.Finite

/-- Proposition 21: extract the integer record inequalities from the checked
finite invariant, without an assumption about the ordering of its table. -/
theorem certified_sharpRecordCondition {s : State} (hs : Certified s) :
    SharpRecordCondition s := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := hs
  have h := Array.all_eq_true.mp sharp_certificate_checked i hi
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- Proposition 21: every choice returned by the recomputed candidate traversal
satisfies the checked lower-diagonal bound. -/
theorem certified_sharpChoiceCondition {s : State} (hs : Certified s)
    {choices : List Choice} (hchoices : calculateChoices Data.historyGraph s = .ok choices)
    {choice : Choice} (hchoice : choice ∈ choices) : SharpChoiceCondition s choice := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := hs
  have h := (Bool.and_eq_true_iff.mp
    (Array.all_eq_true.mp sharp_certificate_checked i hi)).2
  have hchoices' : calculateChoices Data.historyGraph Data.states[i] = .ok choices := hchoices
  have hall : choices.all (fun choice => decide (SharpChoiceCondition Data.states[i] choice)) =
      true := by simpa only [hchoices'] using h
  exact of_decide_eq_true (List.all_eq_true.mp hall choice hchoice)

/-- Section 6.6: a simple rational lower bound for the golden ratio. -/
theorem three_halves_le_goldenRatio : (3 : ℝ) / 2 ≤ Real.goldenRatio := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

/-- Section 6.6: a simple rational upper bound for the golden ratio. -/
theorem goldenRatio_le_five_thirds : Real.goldenRatio ≤ (5 : ℝ) / 3 := by
  nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]

/-- Proposition 21: the exact integer checks imply the required real record
bounds. No numerical approximation to the golden ratio enters this argument. -/
theorem SharpRecordCondition.bounds {s : State} (h : SharpRecordCondition s) :
    -4 ≤ (s.w : ℝ) - ((offsets s.D).card : ℝ) -
      Real.goldenRatio * ((offsets s.R).card : ℝ) ∧
    (s.w : ℝ) - ((offsets s.D).card : ℝ) -
      Real.goldenRatio * ((offsets s.R).card : ℝ) ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := h
  have hlo' : 5 * ((offsets s.R).card : ℝ) ≤
      3 * ((s.w : ℝ) - ((offsets s.D).card : ℝ) + 4) := by exact_mod_cast hlo
  have hhi' : 2 * ((s.w : ℝ) - ((offsets s.D).card : ℝ) - 1) ≤
      3 * ((offsets s.R).card : ℝ) := by exact_mod_cast hhi
  have hnonneg : 0 ≤ ((offsets s.R).card : ℝ) := Nat.cast_nonneg _
  have hmulLo := mul_le_mul_of_nonneg_right three_halves_le_goldenRatio hnonneg
  have hmulHi := mul_le_mul_of_nonneg_right goldenRatio_le_five_thirds hnonneg
  constructor <;> linarith

end Queens.Finite
