import Queens.WindowBounds
import Queens.Finite.RunWitnesses
import Queens.Finite.WindowCertificate

/-!
# Sharper constants and Knuth's ranges

This file formalizes Section 6.6 of *Greedy Queens and the Golden Ratio*:
the asymmetric bound `-4 ≤ d_j - j ≤ 2`, Proposition 24 (finite verification of
the window bounds), and Theorem 2, which proves the ranges that Knuth observed
computationally for the greedy queens.

## Main statements

* `Queens.diagonal_discrepancy_range`: `-4 ≤ d_j - j ≤ 2` for every `j ≥ 1`, and
  `Queens.diagonal_discrepancy_range_attained`: both ends occur.
* `Queens.window_bounds_verified`: **Proposition 24**.
* `Queens.knuth_bounds`: **Theorem 2**.
* `Queens.knuth_ranges`: Theorem 2 in Knuth's 1-indexed coordinates.

## Implementation notes

The proof of Theorem 2 uses only the statement of Proposition 24, Lemma 23,
and the bounds checked directly for `n ≤ 48`. The inequalities of
Proposition 24 hold with `≤`; strictness follows, as in the paper, because
`√5` is irrational and the constants are not attained.
-/

namespace Queens

open scoped goldenRatio

/-- Lemma 17, as used in Section 6.6: before every column `n ≥ 30` with a lower
queen, the actual offset `r = q_n - m` is chosen by a branch of the calculation
on the state `S_n` that describes the board. -/
theorem exists_state_lowerChoice {n : ℕ} (hn : 30 ≤ n) (hlower : q n < n) :
    ∃ s, StateRepresented n s ∧ Finite.Certified s ∧ ∃ choices queue,
      Finite.calculateChoices Finite.Data.historyGraph s = .ok choices ∧
        (some (rowOffset n), queue) ∈ choices := by
  obtain ⟨s, hrep, hcert, hword⟩ := actualInvariant_of_localStepExact local_step_exact n hn
  obtain ⟨next, hnext, -⟩ := Finite.certified_successors hcert
  obtain ⟨queues, choices, hextend, hchoose, -⟩ := Finite.calculate_decompose hnext
  have hm := rowReference_ge_nineteen hn
  obtain ⟨choice, length, -, -, hmatches, hchoice⟩ :=
    local_choices_exact_of_memory (by decide)
      (by simp only [Finite.historyLength]; omega) (countReference_ge_twelve hn)
      hrep (Finite.certified_condition hcert) hword hextend hchoose
  have hactual : choice = some (rowOffset n) := by
    simpa only [ite_eq_left hlower] using hmatches.eq_actual
  exact ⟨s, hrep, hcert, choices, _, Finite.calculateChoices_eq hextend hchoose,
    hactual ▸ hchoice⟩

/-- Section 6.6: every lower queen before column 30 has `d_j - j ≤ 2`.
The finite check uses the Lean kernel. -/
theorem seed_lower_discrepancy_le_two : ∀ n : Fin 30,
    Finite.seedRow n.val < n.val →
    (n.val : ℤ) - Finite.seedRow n.val -
      (((Finset.range (n.val + 1)).filter (fun i => Finite.seedRow i < i)).card : ℤ) ≤ 2 := by
  decide

/-- Section 6.6: the lower-diagonal magnitude of the `(k+1)`st lower queen
exceeds its rank by at most two. Before column 30 this is a direct check;
afterwards `d_j - j = w - r - |D|` is bounded at every lower choice. -/
theorem lowerDiagonal_sub_rank_le_two (k : ℕ) :
    (lowerDiagonal k : ℤ) - ((k : ℤ) + 1) ≤ 2 := by
  have hlower := lowerColumn_lower (infinite_lowerColumns q_surjective) k
  rw [lowerDiagonal_cast]
  by_cases hprefix : lowerColumn k < 30
  · have hsets : (Finset.range (lowerColumn k + 1)).filter (fun i => q i < i) =
        (Finset.range (lowerColumn k + 1)).filter (fun i => Finite.seedRow i < i) := by
      apply Finset.filter_congr
      intro i hi
      rw [Finite.q_eq_seedRow (by have := Finset.mem_range.mp hi; omega)]
    have hcount : ((Finset.range (lowerColumn k + 1)).filter (fun i => q i < i)).card =
        k + 1 := by
      classical
      rw [← Nat.count_eq_card_filter_range]
      exact Nat.count_nth_succ_of_infinite (infinite_lowerColumns q_surjective) k
    have h := seed_lower_discrepancy_le_two ⟨lowerColumn k, hprefix⟩
      (by rwa [← Finite.q_eq_seedRow hprefix])
    rw [← hsets, hcount, ← Finite.q_eq_seedRow hprefix] at h
    push_cast at h
    exact h
  · obtain ⟨s, hrep, hcert, choices, queue, hchoices, hchoice⟩ :=
      exists_state_lowerChoice (by omega) hlower
    have h := (Finite.certified_lowerChoice_bounds hcert hchoices hchoice).2.2
    rw [← hrep.window_eq, ← hrep.diagonalOffsets_eq, ← local_rank_identity hlower,
      nextLowerRank_lowerColumn] at h
    push_cast at h
    exact h

/-- Section 6.6: the asymmetric diagonal discrepancy bound `-4 ≤ d_j - j ≤ 2`
for every `j ≥ 1`. In Lean's zero-based indexing, `j = k + 1`. The lower end
is Lemma 6. -/
theorem diagonal_discrepancy_range (k : ℕ) :
    -4 ≤ (lowerDiagonal k : ℤ) - ((k : ℤ) + 1) ∧
      (lowerDiagonal k : ℤ) - ((k : ℤ) + 1) ≤ 2 :=
  ⟨(abs_le.mp (bounded_diagonal_discrepancy k)).1, lowerDiagonal_sub_rank_le_two k⟩

/-- A lower column preceded by exactly `k` lower columns is the lower column of
zero-based rank `k`. -/
theorem lowerColumn_eq_of_count {x k : ℕ} (hx : q x < x)
    (hcount : Nat.count (fun n => q n < n) x = k) : lowerColumn k = x := by
  rw [← hcount]
  exact Nat.nth_count hx

/-- Before column 5000, lower columns are counted from the verified prefix. -/
theorem count_lower_eq_runWitness {x : ℕ} (hx : x ≤ 5000) :
    Nat.count (fun n => q n < n) x = Nat.count (fun n => Finite.runWitnessRow n < n) x := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [Finite.q_eq_runWitnessRow (by have := Finset.mem_range.mp hi; omega)]

/-- Section 6.6: both ends of `-4 ≤ d_j - j ≤ 2` occur. The 50th lower queen,
in column 131, has `d_j - j = 2`, and the 170th, in column 445, has
`d_j - j = -4`. -/
theorem diagonal_discrepancy_range_attained :
    (lowerDiagonal 49 : ℤ) - (49 + 1) = 2 ∧ (lowerDiagonal 169 : ℤ) - (169 + 1) = -4 := by
  have hq131 : q 131 = 79 := Finite.q_eq_runWitnessRow (by norm_num)
  have hq445 : q 445 = 279 := Finite.q_eq_runWitnessRow (by norm_num)
  have h49 : lowerColumn 49 = 131 := by
    apply lowerColumn_eq_of_count (by omega)
    rw [count_lower_eq_runWitness (by norm_num)]
    decide +kernel
  have h169 : lowerColumn 169 = 445 := by
    apply lowerColumn_eq_of_count (by omega)
    rw [count_lower_eq_runWitness (by norm_num)]
    decide +kernel
  simp only [lowerDiagonal, h49, h169, hq131, hq445]
  norm_num

/-- Proposition 24(i): the window bounds at every vertex `W` whose last symbol
has column bit 1 lie between `(19√5 - 49) / 8` and `√5 - 1`. -/
def UpperWindowBounds (lo hi : ℕ → ℝ) : Prop :=
  ∀ W ∈ Finite.Data.historyGraph.map Prod.fst, Finite.upperBit (W % 4) = 1 →
    (19 * Real.sqrt 5 - 49) / 8 ≤ lo W ∧ hi W ≤ Real.sqrt 5 - 1

/-- Proposition 24(ii): if a branch of the calculation on a state `S` of the
state graph chooses a lower queen at offset `r`, then with `V = H_in(S)`,
`15 - 8√5 ≤ r + 1 / φ² - (z + hi(V)) / φ` and
`r + 1 / φ² - (z + lo(V)) / φ ≤ 13 - 4√5`. -/
def LowerChoiceWindowBounds (lo hi : ℕ → ℝ) : Prop :=
  ∀ s, Relation.ReflTransGen Finite.Step Finite.initialState s →
    ∀ choices, Finite.calculateChoices Finite.Data.historyGraph s = .ok choices →
      ∀ r queue, (some r, queue) ∈ choices →
        15 - 8 * Real.sqrt 5 ≤ (r : ℝ) + 1 / φ ^ 2 - ((s.z : ℝ) + hi s.input) / φ ∧
          (r : ℝ) + 1 / φ ^ 2 - ((s.z : ℝ) + lo s.input) / φ ≤ 13 - 4 * Real.sqrt 5

/-- **Proposition 24 (finite verification of the window bounds).** There are
consistent functions `lo` and `hi` with values in `ℚ(√5)`, satisfying the
hypothesis of Lemma 23, with properties (i) and (ii). -/
theorem window_bounds_verified : ∃ lo hi : ℕ → ℝ,
    (∀ W, ∃ a b : ℚ, lo W = a + b * Real.sqrt 5) ∧
    (∀ W, ∃ a b : ℚ, hi W = a + b * Real.sqrt 5) ∧
    ConsistentWindowBounds lo hi ∧
    (∀ n, 30 ≤ n → n ≤ 48 → WindowBoundsHold lo hi n) ∧
    UpperWindowBounds lo hi ∧ LowerChoiceWindowBounds lo hi := by
  refine ⟨Finite.windowLo, Finite.windowHi, Finite.windowLo_mem_sqrtFive,
    Finite.windowHi_mem_sqrtFive, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact Finite.certified_windowConsistent (Finite.certified_iff_reachable.mpr hs)
  · intro n h30 h48
    exact Finite.window_bounds_start h30 h48
  · intro W hW hupper
    exact Finite.upper_window_bounds hW hupper
  · intro s hs choices hchoices r queue hchoice
    obtain ⟨hlo, hhi, -⟩ :=
      Finite.certified_lowerChoice_bounds (Finite.certified_iff_reachable.mpr hs) hchoices hchoice
    exact ⟨hlo, hhi⟩

/-- The last symbol of the window `σ_{n-11} … σ_n` is `σ_n`. -/
theorem outputWindow_succ_mod_four {n : ℕ} (hn : 11 ≤ n) :
    outputWindow (n + 1) % 4 = queenSymbol n := by
  have hsymbol := queenSymbol_lt_four n
  simp only [outputWindow, Finite.historyWindow, Finite.historyLength, Nat.add_sub_cancel]
  rw [show List.range 12 = List.range 11 ++ [11] from List.range_succ, List.map_append,
    Finite.encode, List.foldl_append]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    show n + 1 - 12 + 11 = n by omega]
  omega

/-- Section 6.6: at an upper column, `q_n - n φ = ε(n)` by Lemma 3. -/
theorem upper_position_error_eq_countError {n : ℕ} (hn : n < q n) :
    (q n : ℝ) - (n : ℝ) * φ = countError upperCount n :=
  upper_position_error_eq upperCount (q n) n (q_eq_add_upperCount hn)

/-- Section 6.6, proof of Theorem 2: at a lower column `n ≥ 1` with least
unused row `m` and record `z`, `q_n - n / φ = r + 1 / φ² - (z + ε(m - 1)) / φ`. -/
theorem lower_position_error_eq_offset {n : ℕ} (hn : 0 < n) :
    (q n : ℝ) - (n : ℝ) / φ = (rowOffset n : ℝ) + 1 / φ ^ 2 -
      ((upperDisplacement n : ℝ) + countError upperCount (rowReference n - 1)) / φ := by
  have hcolumn : (n : ℝ) = (rowReference n : ℝ) + (upperCount (rowReference n - 1) : ℝ) +
      (upperDisplacement n : ℝ) := by
    exact_mod_cast column_eq_reference_add_displacement n
  have hrow : (q n : ℝ) = (rowReference n : ℝ) + (rowOffset n : ℝ) := by
    have := rowReference_le_q n
    unfold rowOffset
    push_cast [this]
    ring
  have hm : 1 ≤ rowReference n := rowReference_pos hn
  have hinv := inv_goldenRatio_sq
  rw [countError, Nat.cast_sub hm, Nat.cast_one, one_div, ← inv_pow]
  linear_combination hrow - φ⁻¹ * hcolumn - (rowReference n : ℝ) * hinv

/-- Theorem 2 for upper queens, with `≤` in place of `<`. -/
theorem upper_position_bounds {n : ℕ} (hupper : n < q n) :
    (19 * Real.sqrt 5 - 49) / 8 ≤ (q n : ℝ) - n * φ ∧
      (q n : ℝ) - n * φ ≤ Real.sqrt 5 - 1 := by
  by_cases hdirect : n < 49
  · exact Finite.first_upper_position_bounds hdirect hupper
  obtain ⟨lo, hi, -, -, hconsistent, hstart, hupperWindow, -⟩ := window_bounds_verified
  obtain ⟨hlo, hhi⟩ := window_bounds_hold hconsistent hstart (n + 1) (by omega)
  obtain ⟨-, -, -, hword⟩ := actualInvariant_of_localStepExact local_step_exact (n + 1) (by omega)
  have hvertex : outputWindow (n + 1) ∈ Finite.Data.historyGraph.map Prod.fst :=
    (hword n (Finset.mem_Icc.mpr ⟨by simp [Finite.historyLength]; omega, by omega⟩)).1
  have hbit : Finite.upperBit (outputWindow (n + 1) % 4) = 1 := by
    rw [outputWindow_succ_mod_four (by omega), upperBit_queenSymbol, columnBit, ite_eq_left hupper]
  obtain ⟨hbelow, habove⟩ := hupperWindow _ hvertex hbit
  rw [upper_position_error_eq_countError hupper]
  simp only [Nat.add_sub_cancel] at hlo hhi
  exact ⟨hbelow.trans hlo, hhi.trans habove⟩

/-- Theorem 2 for lower queens, with `≤` in place of `<`. -/
theorem lower_position_bounds {n : ℕ} (hlower : q n < n) :
    15 - 8 * Real.sqrt 5 ≤ (q n : ℝ) - n / φ ∧
      (q n : ℝ) - n / φ ≤ 13 - 4 * Real.sqrt 5 := by
  by_cases hdirect : n < 49
  · exact Finite.first_lower_position_bounds hdirect hlower
  obtain ⟨lo, hi, -, -, hconsistent, hstart, -, hchoiceWindow⟩ := window_bounds_verified
  obtain ⟨hm, hmn, -, t, -, -, ht, -⟩ := exists_linked_states (n := n) (by omega)
  obtain ⟨s, hs, hcert, choices, queue, hchoices, hchoice⟩ :=
    exists_state_lowerChoice (by omega) hlower
  have hlink := input_eq_output_of_represented hs ht
  obtain ⟨hlo, hhi⟩ := window_bounds_hold hconsistent hstart _ hm
  rw [← ht.output_eq_outputWindow, ← hlink] at hlo hhi
  obtain ⟨hbelow, habove⟩ :=
    hchoiceWindow s (Finite.certified_iff_reachable.mp hcert) choices hchoices _ queue hchoice
  rw [← hs.upperDisplacement_eq] at hbelow habove
  rw [lower_position_error_eq_offset (by omega)]
  have hphi := Real.goldenRatio_pos
  constructor
  · calc 15 - 8 * Real.sqrt 5
        ≤ _ - ((upperDisplacement n : ℝ) + hi s.input) / φ := hbelow
      _ ≤ _ := by gcongr
  · calc _ ≤ (rowOffset n : ℝ) + 1 / φ ^ 2 - ((upperDisplacement n : ℝ) + lo s.input) / φ := by
          gcongr
      _ ≤ 13 - 4 * Real.sqrt 5 := habove

/-- `q_n - n φ`, scaled by 8, is the value of an element of `ℤ√5` whose `√5`
coefficient is `-4n`. -/
theorem upper_position_error_eq_eval (n : ℕ) :
    8 * ((q n : ℝ) - n * φ) = sqrtFiveEval ⟨8 * q n - 4 * n, -4 * n⟩ := by
  rw [sqrtFiveEval_apply, goldenRatio_eq]
  push_cast
  ring

/-- `q_n - n / φ`, scaled by 2, is the value of an element of `ℤ√5` whose `√5`
coefficient is `-n`. -/
theorem lower_position_error_eq_eval (n : ℕ) :
    2 * ((q n : ℝ) - n / φ) = sqrtFiveEval ⟨2 * q n + n, -n⟩ := by
  rw [sqrtFiveEval_apply, div_eq_mul_inv, inv_goldenRatio_eq]
  push_cast
  ring

/-- Section 6.6, proof of Theorem 2: `q_n - n φ = (q_n - n / 2) - (n / 2) √5` has a
nonpositive coefficient of `√5`, so it never equals `(a + b√5) / 8` with `b > 0`. -/
theorem upper_position_error_ne {n : ℕ} {a b : ℤ} (hb : 0 < b) :
    (q n : ℝ) - n * φ ≠ (a + b * Real.sqrt 5) / 8 := by
  intro heq
  have h := sqrtFiveEval_injective (a₁ := ⟨8 * q n - 4 * n, -4 * n⟩) (a₂ := ⟨a, b⟩)
    (by rw [← upper_position_error_eq_eval, heq, sqrtFiveEval_apply]; ring)
  have him := congrArg Zsqrtd.im h
  simp only at him
  omega

/-- Section 6.6, proof of Theorem 2: `q_n - n / φ = (q_n + n / 2) - (n / 2) √5`
determines `n` and `q_n`. If it equals `(a + b√5) / 2`, then `n = -b` and
`2 q_n + n = a`. -/
theorem lower_position_error_eq_imp {n : ℕ} {a b : ℤ}
    (heq : (q n : ℝ) - n / φ = (a + b * Real.sqrt 5) / 2) :
    (n : ℤ) = -b ∧ 2 * (q n : ℤ) + n = a := by
  have h := sqrtFiveEval_injective (a₁ := ⟨2 * q n + n, -n⟩) (a₂ := ⟨a, b⟩)
    (by rw [← lower_position_error_eq_eval, heq, sqrtFiveEval_apply]; ring)
  have hre := congrArg Zsqrtd.re h
  have him := congrArg Zsqrtd.im h
  simp only at hre him
  omega

/-- **Theorem 2.** For every `n ≥ 1`, the greedy queens satisfy
`(19√5 - 49) / 8 < q_n - n φ < √5 - 1` if `q_n > n`, and
`15 - 8√5 < q_n - n / φ < 13 - 4√5` if `q_n < n`. The statement also covers
`n = 0`, where both implications have false antecedents. -/
theorem knuth_bounds (n : ℕ) :
    (n < q n → (19 * Real.sqrt 5 - 49) / 8 < (q n : ℝ) - n * Real.goldenRatio ∧
      (q n : ℝ) - n * Real.goldenRatio < Real.sqrt 5 - 1) ∧
    (q n < n → 15 - 8 * Real.sqrt 5 < (q n : ℝ) - n / Real.goldenRatio ∧
      (q n : ℝ) - n / Real.goldenRatio < 13 - 4 * Real.sqrt 5) := by
  constructor
  · intro hupper
    obtain ⟨hlo, hhi⟩ := upper_position_bounds hupper
    -- Both constants have a positive coefficient of `√5`, so neither is attained.
    refine ⟨lt_of_le_of_ne hlo fun heq => ?_, lt_of_le_of_ne hhi fun heq => ?_⟩
    · exact upper_position_error_ne (a := -49) (b := 19) (by norm_num)
        (by rw [← heq]; push_cast; ring)
    · exact upper_position_error_ne (a := -8) (b := 8) (by norm_num)
        (by rw [heq]; push_cast; ring)
  · intro hlower
    obtain ⟨hlo, hhi⟩ := lower_position_bounds hlower
    -- Equality is possible only at `n = 16` or `n = 8`, both upper columns.
    have hq8 : q 8 = 14 := Finite.q_eq_firstRow (by norm_num)
    have hq16 : q 16 = 26 := Finite.q_eq_firstRow (by norm_num)
    refine ⟨lt_of_le_of_ne hlo fun heq => ?_, lt_of_le_of_ne hhi fun heq => ?_⟩
    · obtain ⟨hn, -⟩ := lower_position_error_eq_imp (a := 30) (b := -16)
        (by rw [← heq]; push_cast; ring)
      obtain rfl : n = 16 := by omega
      omega
    · obtain ⟨hn, -⟩ := lower_position_error_eq_imp (a := 26) (b := -8)
        (by rw [heq]; push_cast; ring)
      obtain rfl : n = 8 := by omega
      omega

/-- Knuth's 1-indexed coordinates: the queen in column `c = n + 1` lies on row
`s(c) = q_n + 1`. -/
noncomputable def knuthRow (c : ℕ) : ℕ := q (c - 1) + 1

/-- **Theorem 2, in Knuth's coordinates.** For every `c ≥ 1`,
`s(c) ∈ [c / φ - 3 .. c / φ + 5] ∪ [c φ - 2 .. c φ + 1]`, the ranges that Knuth
observed for `c ≤ 10⁹`. Since `s(c)` is an integer, membership in the paper's
integer intervals is membership in the real intervals below. -/
theorem knuth_ranges {c : ℕ} (hc : 1 ≤ c) :
    (knuthRow c : ℝ) ∈ Set.Icc (c / Real.goldenRatio - 3) (c / Real.goldenRatio + 5) ∪
      Set.Icc (c * Real.goldenRatio - 2) (c * Real.goldenRatio + 1) := by
  have hsqrt_lo : (2.2 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hsqrt_hi : Real.sqrt 5 ≤ 2.25 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hinv := inv_goldenRatio_eq
  obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  simp only [knuthRow, Nat.add_sub_cancel, Set.mem_union, Set.mem_Icc]
  push_cast
  rw [div_eq_mul_inv ((n : ℝ) + 1) φ, hinv]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    simp only [q_zero, CharP.cast_eq_zero, zero_add, one_mul]
    constructor <;> linarith
  rcases lt_or_gt_of_ne (q_ne_self hn) with hlower | hupper
  · obtain ⟨hlo, hhi⟩ := (knuth_bounds n).2 hlower
    rw [div_eq_mul_inv, hinv] at hlo hhi
    left
    constructor <;> linarith
  · obtain ⟨hlo, hhi⟩ := (knuth_bounds n).1 hupper
    rw [goldenRatio_eq] at hlo hhi ⊢
    right
    constructor <;> linarith

end Queens
