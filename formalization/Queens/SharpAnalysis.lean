import Queens.GoldenRatio
import Queens.Finite.Seed

/-!
# Initial estimates for the sharper constants

This file proves Proposition 21's starting bounds using the verified first
thirty greedy queens and rational bounds for `φ`. The contraction argument
for arbitrary real sequences is in `Queens.GoldenRatio`; `Queens.SharperBounds`
combines it with these initial bounds and the recursion of Lemma 20.
-/

namespace Queens

open scoped goldenRatio

namespace Finite

/-- The upper count read from the verified seed table. This is used only
to establish Proposition 21's initial inequalities. -/
def seedUpperCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun i => i < seedRow i)).card

/-- In the first thirty columns the seed upper count equals the actual
upper count, by the greedy-prefix identification in Section 6.1. -/
theorem upperCount_eq_seedUpperCount {n : ℕ} (hn : n < 30) :
    upperCount n = seedUpperCount n := by
  unfold upperCount seedUpperCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [q_eq_seedRow (by have := Finset.mem_range.mp hi; omega)]

private theorem seed_count_integer_bounds : ∀ n : Fin 30,
    -3000 < 1618 * (seedUpperCount n : ℤ) - 1000 * (n : ℤ) ∧
      1619 * (seedUpperCount n : ℤ) - 1000 * (n : ℤ) < 2000 := by
  decide

/-- Proposition 21's base cases, proved by exact integer computation and
rational bounds on the golden ratio. The proof uses kernel reduction only. -/
theorem prefix_sharp_count_error {n : ℕ} (hn : n < 30) :
    -3 / φ < countError upperCount n ∧ countError upperCount n < 2 / φ := by
  have hphi := Real.goldenRatio_sq
  have hp := Real.goldenRatio_pos
  have hlo : (1618 : ℝ) / 1000 < φ := by nlinarith
  have hhi : φ < (1619 : ℝ) / 1000 := by nlinarith
  have hu : (0 : ℝ) ≤ seedUpperCount n := Nat.cast_nonneg _
  have hchecked := seed_count_integer_bounds ⟨n, hn⟩
  have hl : (-3000 : ℝ) < 1618 * (seedUpperCount n : ℝ) - 1000 * (n : ℝ) := by
    exact_mod_cast hchecked.1
  have hh : 1619 * (seedUpperCount n : ℝ) - 1000 * (n : ℝ) < (2000 : ℝ) := by
    exact_mod_cast hchecked.2
  have hleft := mul_le_mul_of_nonneg_right hlo.le hu
  have hright := mul_le_mul_of_nonneg_right hhi.le hu
  have hmul : countError upperCount n * φ = (seedUpperCount n : ℝ) * φ - n := by
    rw [countError, upperCount_eq_seedUpperCount hn]
    have hinv : φ⁻¹ * φ = 1 := inv_mul_cancel₀ Real.goldenRatio_ne_zero
    calc
      ((seedUpperCount n : ℝ) - φ⁻¹ * (n : ℝ)) * φ =
          (seedUpperCount n : ℝ) * φ - (φ⁻¹ * φ) * (n : ℝ) := by ring
      _ = _ := by rw [hinv, one_mul]
  constructor
  · apply (div_lt_iff₀ hp).mpr
    rw [hmul]
    nlinarith
  · apply (lt_div_iff₀ hp).mpr
    rw [hmul]
    nlinarith

end Finite

end Queens
