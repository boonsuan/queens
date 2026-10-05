import Queens.SqrtFive
import Queens.LocalAdvances
import Queens.Finite.GreedyPrefix
import Queens.Finite.PrefixTransfer

/-!
# The columns before 49

Section 6.6 treats the columns before 49 directly. Lemma 23 uses that the least
unused row before column 49 is at least 30, and the proof of Theorem 2 checks
its bounds directly for `1 ≤ n ≤ 48`. This file verifies the rows `q₀, …, q₄₈`
with the proved bitboard checker of `Queens.Finite.GreedyPrefix`, so the table
below is data identified with the actual sequence `q`, not an assumption.

## Main statements

* `Queens.Finite.q_eq_firstRow`: the table agrees with `q` before column 49.
* `Queens.Finite.thirty_le_rowReference`: `m ≥ 30` before every column `n ≥ 49`.
* `Queens.Finite.first_upper_position_bounds`,
  `Queens.Finite.first_lower_position_bounds`: the non-strict bounds of
  Theorem 2 for `1 ≤ n ≤ 48`.
-/

namespace Queens.Finite

open scoped goldenRatio

/-- Section 6.6: the rows `q₀, …, q₄₈` of the first 49 columns. -/
def firstRows : List ℕ :=
  [0, 2, 4, 1, 3, 8, 10, 12, 14, 5,
   7, 18, 6, 21, 9, 24, 26, 28, 30, 11,
   13, 34, 36, 38, 40, 15, 17, 44, 16, 47,
   19, 50, 52, 20, 55, 57, 59, 22, 62, 23,
   65, 27, 25, 69, 71, 73, 75, 77, 29]

/-- Section 6.6: read an entry of the table of the first 49 rows. -/
def firstRow (n : ℕ) : ℕ := firstRows[n]?.getD 0

/-- Section 6.6: the bitboard checker accepts every row of the table: each is
unattacked by the earlier rows, and every smaller row is attacked. -/
theorem firstRows_checked : AttackBoard.empty.checkRows firstRows = true := by
  decide +kernel

/-- Section 6.6: the table agrees with the actual greedy sequence before
column 49. -/
theorem q_eq_firstRow {n : ℕ} (hn : n < 49) : q n = firstRow n := by
  have h := AttackBoard.empty_represents.q_eq_of_checkRows firstRows_checked ⟨n, hn⟩
  simpa [firstRow, List.getElem?_eq_getElem (show n < firstRows.length from hn)] using h

/-- Definition 10 evaluated on the first 49 columns. -/
def firstSymbol (n : ℕ) : ℕ :=
  2 * (if n < firstRow n then 1 else 0) +
    if ∃ i : Fin n, i.val < firstRow i.val ∧ firstRow i.val = n then 1 else 0

/-- Section 6.6: the queen word before index 49, read from the table. -/
theorem queenSymbol_eq_firstSymbol {n : ℕ} (hn : n < 49) :
    queenSymbol n = firstSymbol n :=
  queenSymbol_eq_of_prefix (fun i hi => q_eq_firstRow (by omega))

/-- The upper count `U(n)` read from the table of the first 49 rows. -/
def firstUpperCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun i => i < firstRow i)).card

/-- Section 6.6: the upper count before column 49, read from the table. -/
theorem upperCount_eq_firstUpperCount {n : ℕ} (hn : n < 49) :
    upperCount n = firstUpperCount n :=
  upperCount_eq_of_prefix (fun i hi => q_eq_firstRow (by omega))

/-- Section 6.6: the least unused row before column 49 is 31. -/
theorem rowReference_fortyNine : rowReference 49 = 31 := by
  unfold rowReference
  rw [occupiedRows_eq_of_prefix (rows := firstRow) (fun _ hi => q_eq_firstRow hi)]
  apply leastUnused_eq_of_spec
  · decide
  · have hfinite : ∀ r : Fin 31, r.val ∈ (Finset.range 49).image firstRow := by decide
    intro r hr
    exact hfinite ⟨r, hr⟩

/-- Section 6.6, proof of Lemma 23: before every column `n ≥ 49` the least
unused row is at least 30, since it never decreases. -/
theorem thirty_le_rowReference {n : ℕ} (hn : 49 ≤ n) : 30 ≤ rowReference n := by
  have h := rowReference_mono hn
  rw [rowReference_fortyNine] at h
  omega

/-- `8 (q - n φ) = (8 q - 4 n) - 4 n √5` as an element of `ℤ√5`. -/
def scaledUpperPositionError (n row : ℕ) : ZSqrtFive :=
  ⟨8 * row - 4 * n, -4 * n⟩

/-- `2 (q - n / φ) = (2 q + n) - n √5` as an element of `ℤ√5`. -/
def scaledLowerPositionError (n row : ℕ) : ZSqrtFive :=
  ⟨2 * row + n, -n⟩

/-- Theorem 2 for the columns `1 ≤ n ≤ 48`, multiplied by 8 for upper queens and
by 2 for lower queens, and checked by kernel reduction. -/
theorem firstRows_position_checked : ∀ n : Fin 49, 1 ≤ n.val →
    (n.val < firstRow n.val →
      (⟨-49, 19⟩ : ZSqrtFive) ≤ scaledUpperPositionError n (firstRow n) ∧
        scaledUpperPositionError n (firstRow n) ≤ ⟨-8, 8⟩) ∧
    (firstRow n.val < n.val →
      (⟨30, -16⟩ : ZSqrtFive) ≤ scaledLowerPositionError n (firstRow n) ∧
        scaledLowerPositionError n (firstRow n) ≤ ⟨26, -8⟩) := by
  decide +kernel

/-- Theorem 2 for upper queens in the columns `1 ≤ n ≤ 48`, with `≤` in place
of `<`: `(19√5 - 49) / 8 ≤ q_n - n φ ≤ √5 - 1`. -/
theorem first_upper_position_bounds {n : ℕ} (hn : n < 49) (hupper : n < q n) :
    (19 * Real.sqrt 5 - 49) / 8 ≤ (q n : ℝ) - n * φ ∧
      (q n : ℝ) - n * φ ≤ Real.sqrt 5 - 1 := by
  have hpos : 1 ≤ n := by
    by_contra h
    obtain rfl : n = 0 := by omega
    simp at hupper
  rw [q_eq_firstRow hn] at hupper ⊢
  obtain ⟨hlo, hhi⟩ := (firstRows_position_checked ⟨n, hn⟩ hpos).1 hupper
  have hlo' := sqrtFiveEval_le hlo
  have hhi' := sqrtFiveEval_le hhi
  simp only [sqrtFiveEval_apply, scaledUpperPositionError] at hlo' hhi'
  push_cast at hlo' hhi'
  rw [goldenRatio_eq]
  constructor <;> linarith

/-- Theorem 2 for lower queens in the columns `1 ≤ n ≤ 48`, with `≤` in place
of `<`: `15 - 8√5 ≤ q_n - n / φ ≤ 13 - 4√5`. -/
theorem first_lower_position_bounds {n : ℕ} (hn : n < 49) (hlower : q n < n) :
    15 - 8 * Real.sqrt 5 ≤ (q n : ℝ) - n / φ ∧
      (q n : ℝ) - n / φ ≤ 13 - 4 * Real.sqrt 5 := by
  have hpos : 1 ≤ n := by omega
  rw [q_eq_firstRow hn] at hlower ⊢
  obtain ⟨hlo, hhi⟩ := (firstRows_position_checked ⟨n, hn⟩ hpos).2 hlower
  have hlo' := sqrtFiveEval_le hlo
  have hhi' := sqrtFiveEval_le hhi
  simp only [sqrtFiveEval_apply, scaledLowerPositionError] at hlo' hhi'
  push_cast at hlo' hhi'
  rw [div_eq_mul_inv, inv_goldenRatio_eq]
  constructor <;> linarith

end Queens.Finite
