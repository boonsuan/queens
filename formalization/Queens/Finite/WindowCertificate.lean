import Queens.GoldenRatio
import Queens.Finite.Certificate
import Queens.Finite.FirstColumns
import Queens.Finite.History
import Queens.Finite.WindowChunks
import Queens.Finite.WindowVertexChecks

/-!
# The checked window bounds

This file extracts the content of Proposition 24 (finite verification of the
window bounds, Section 6.6) from the kernel-checked finite checks. It defines
the window bounds `lo` and `hi` as real functions on encoded twelve-symbol
words, read from the generated table, and proves their properties at every
state of the state graph and every vertex of the history graph.

The same checks establish two statements made in the text: every twelve
consecutive symbols of `H_in Q`, and `H_out`, form a vertex (Section 4.3), and
every vertex is the output history of some state (Section 6.6).

## Main statements

* `Queens.Finite.certified_windowConsistent`: the inequalities of Definition 22.
* `Queens.Finite.certified_lowerChoice_bounds`: Proposition 24(ii), and
  `w - r - |D| ≤ 2` at every lower choice.
* `Queens.Finite.upper_window_bounds`: Proposition 24(i).
* `Queens.Finite.window_bounds_start`: the hypothesis of Lemma 23 for
  `30 ≤ n ≤ 48`.

## Implementation notes

`windowLo` and `windowHi` are defined on all natural numbers; only their values
at vertices of the history graph matter, and `graphVertex_windowBound` shows that
every vertex has an entry in the table.
-/

namespace Queens.Finite

open scoped goldenRatio

/-- Section 6.6: the lower window bound `lo(W)` read from the checked table,
with the arbitrary value `0` away from the vertices. -/
noncomputable def windowLo (vertex : ℕ) : ℝ :=
  ((windowBound? vertex).map fun bound => sqrtFiveEval bound.lo / 8).getD 0

/-- Section 6.6: the upper window bound `hi(W)` read from the checked table,
with the arbitrary value `0` away from the vertices. -/
noncomputable def windowHi (vertex : ℕ) : ℝ :=
  ((windowBound? vertex).map fun bound => sqrtFiveEval bound.hi / 8).getD 0

/-- At a vertex with a table entry, `lo(W)` is one eighth of the stored value. -/
theorem windowLo_of_lookup {vertex : ℕ} {bound : WindowBound}
    (h : windowBound? vertex = some bound) : windowLo vertex = sqrtFiveEval bound.lo / 8 := by
  simp [windowLo, h]

/-- At a vertex with a table entry, `hi(W)` is one eighth of the stored value. -/
theorem windowHi_of_lookup {vertex : ℕ} {bound : WindowBound}
    (h : windowBound? vertex = some bound) : windowHi vertex = sqrtFiveEval bound.hi / 8 := by
  simp [windowHi, h]

/-- Proposition 24: the lower window bounds lie in `ℚ(√5)`. -/
theorem windowLo_mem_sqrtFive (vertex : ℕ) : ∃ a b : ℚ, windowLo vertex = a + b * Real.sqrt 5 := by
  cases h : windowBound? vertex with
  | none => exact ⟨0, 0, by simp [windowLo, h]⟩
  | some bound =>
    refine ⟨bound.lo.re / 8, bound.lo.im / 8, ?_⟩
    rw [windowLo_of_lookup h, sqrtFiveEval_apply]
    push_cast
    ring

/-- Proposition 24: the upper window bounds lie in `ℚ(√5)`. -/
theorem windowHi_mem_sqrtFive (vertex : ℕ) : ∃ a b : ℚ, windowHi vertex = a + b * Real.sqrt 5 := by
  cases h : windowBound? vertex with
  | none => exact ⟨0, 0, by simp [windowHi, h]⟩
  | some bound =>
    refine ⟨bound.hi.re / 8, bound.hi.im / 8, ?_⟩
    rw [windowHi_of_lookup h, sqrtFiveEval_apply]
    push_cast
    ring

/-- `2 / φ = √5 - 1`, evaluated. -/
theorem sqrtFiveEval_twiceInvGoldenRatio : sqrtFiveEval twiceInvGoldenRatio = 2 * φ⁻¹ := by
  rw [sqrtFiveEval_apply, inv_goldenRatio_eq]
  simp [twiceInvGoldenRatio]
  ring

/-- The scaled error term evaluates to `16 Y(S)`. -/
theorem sqrtFiveEval_scaledErrorTerm (s : State) :
    sqrtFiveEval (scaledErrorTerm s) = 16 * errorTerm s := by
  rw [sqrtFiveEval_apply, errorTerm, div_eq_mul_inv, inv_goldenRatio_eq]
  simp [scaledErrorTerm]
  ring

/-- The scaled lower base evaluates to `16 (r + 1 / φ² - z / φ)`. -/
theorem sqrtFiveEval_scaledLowerBase (s : State) (r : ℕ) :
    sqrtFiveEval (scaledLowerBase s r) = 16 * ((r : ℝ) + 1 / φ ^ 2 - (s.z : ℝ) / φ) := by
  rw [sqrtFiveEval_apply, one_div, ← inv_pow, div_eq_mul_inv, inv_goldenRatio_eq]
  simp [scaledLowerBase]
  ring_nf
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- Proposition 24: every certified state passes the window check. -/
theorem certified_checkWindowState {s : State} (hs : Certified s) : checkWindowState s = true := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := hs
  exact Array.all_eq_true.mp windowStates_checked i hi

/-- Proposition 24: unpack the window check of a certified state. -/
theorem certified_windowBound {s : State} (hs : Certified s) :
    checkStateHistories s = true ∧
      ∃ input output, windowBound? s.input = some input ∧ windowBound? s.output = some output ∧
        ConsistentAt s input output ∧
        ∀ choices, calculateChoices Data.historyGraph s = .ok choices →
          ∀ r queue, (some r, queue) ∈ choices → LowerChoiceBounds s input r := by
  have h := certified_checkWindowState hs
  unfold checkWindowState at h
  obtain ⟨hhist, h⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨hhist, ?_⟩
  cases hin : windowBound? s.input with
  | none => simp [hin] at h
  | some input =>
    cases hout : windowBound? s.output with
    | none => simp [hin, hout] at h
    | some output =>
      simp only [hin, hout, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hcons, hchoices⟩ := h
      refine ⟨input, output, rfl, rfl, hcons, ?_⟩
      intro choices hcalc r queue hmem
      rw [hcalc] at hchoices
      have := List.all_eq_true.mp hchoices _ hmem
      simpa using this

/-- **Definition 22 at every state of the state graph.** With `V = H_in(S)` and
`W = H_out(S)`, the checked window bounds satisfy
`lo(W) ≤ Y(S) - hi(V) / φ` and `Y(S) - lo(V) / φ ≤ hi(W)`. -/
theorem certified_windowConsistent {s : State} (hs : Certified s) :
    windowLo s.output ≤ errorTerm s - windowHi s.input / φ ∧
      errorTerm s - windowLo s.input / φ ≤ windowHi s.output := by
  obtain ⟨-, input, output, hin, hout, ⟨hlo, hhi⟩, -⟩ := certified_windowBound hs
  have hlo' := sqrtFiveEval_le hlo
  have hhi' := sqrtFiveEval_le hhi
  rw [map_mul, map_sub, map_mul, sqrtFiveEval_scaledErrorTerm,
    sqrtFiveEval_twiceInvGoldenRatio, map_ofNat] at hlo'
  rw [map_mul, map_sub, map_mul, sqrtFiveEval_scaledErrorTerm,
    sqrtFiveEval_twiceInvGoldenRatio, map_ofNat] at hhi'
  have hscale (x : ℝ) : errorTerm s - x / 8 / φ =
      (16 * errorTerm s - x * (2 * φ⁻¹)) / 16 := by
    rw [div_eq_mul_inv _ φ]
    ring
  rw [windowLo_of_lookup hout, windowHi_of_lookup hin, windowLo_of_lookup hin,
    windowHi_of_lookup hout, hscale, hscale]
  constructor <;> linarith

/-- **Proposition 24(ii)** at every state of the state graph, together with the
bound `w - r - |D| ≤ 2` of Section 6.6. If a branch of the calculation chooses
a lower queen at offset `r`, then with `V = H_in(S)`,
`15 - 8√5 ≤ r + 1 / φ² - (z + hi(V)) / φ` and
`r + 1 / φ² - (z + lo(V)) / φ ≤ 13 - 4√5`. -/
theorem certified_lowerChoice_bounds {s : State} (hs : Certified s) {choices : List Choice}
    (hchoices : calculateChoices Data.historyGraph s = .ok choices)
    {r : ℕ} {queue : List ℕ} (hchoice : (some r, queue) ∈ choices) :
    15 - 8 * Real.sqrt 5 ≤ (r : ℝ) + 1 / φ ^ 2 - ((s.z : ℝ) + windowHi s.input) / φ ∧
      (r : ℝ) + 1 / φ ^ 2 - ((s.z : ℝ) + windowLo s.input) / φ ≤ 13 - 4 * Real.sqrt 5 ∧
      s.w - r - ((offsets s.D).card : ℤ) ≤ 2 := by
  obtain ⟨-, input, -, hin, -, -, hall⟩ := certified_windowBound hs
  obtain ⟨hlo, hhi, hdisc⟩ := hall choices hchoices r queue hchoice
  have hlo' := sqrtFiveEval_le hlo
  have hhi' := sqrtFiveEval_le hhi
  have hbelow : sqrtFiveEval ⟨240, -128⟩ = 240 - 128 * Real.sqrt 5 := by simp; ring
  have habove : sqrtFiveEval ⟨208, -64⟩ = 208 - 64 * Real.sqrt 5 := by simp; ring
  rw [hbelow, map_sub, map_mul, sqrtFiveEval_scaledLowerBase,
    sqrtFiveEval_twiceInvGoldenRatio] at hlo'
  rw [habove, map_sub, map_mul, sqrtFiveEval_scaledLowerBase,
    sqrtFiveEval_twiceInvGoldenRatio] at hhi'
  have hscale (x : ℝ) : (r : ℝ) + 1 / φ ^ 2 - ((s.z : ℝ) + x / 8) / φ =
      (16 * ((r : ℝ) + 1 / φ ^ 2 - (s.z : ℝ) / φ) - x * (2 * φ⁻¹)) / 16 := by
    simp only [div_eq_mul_inv]
    ring
  rw [windowHi_of_lookup hin, windowLo_of_lookup hin, hscale, hscale]
  exact ⟨by linarith, by linarith, hdisc⟩

/-- Section 4.3: for every state of the state graph, every twelve consecutive
symbols of `H_in Q` form a vertex. Here `inputWindow s k` encodes the twelve
symbols ending after the first `k` symbols of `Q`. -/
theorem certified_inputWindow_mem {s : State} (hs : Certified s) {k : ℕ}
    (hk : k ≤ s.queue.length) : inputWindow s k ∈ Data.historyGraph.map Prod.fst := by
  have h := (certified_windowBound hs).1
  unfold checkStateHistories at h
  obtain ⟨hwindows, -⟩ := Bool.and_eq_true_iff.mp h
  exact HistoryGraph.mem_of_lookup_isSome
    (List.all_eq_true.mp hwindows k (List.mem_range.mpr (by omega)))

/-- Section 4.3: the input history of every state of the state graph is a vertex. -/
theorem certified_input_mem {s : State} (hs : Certified s) :
    s.input ∈ Data.historyGraph.map Prod.fst :=
  certified_inputWindow_mem hs (Nat.zero_le _)

/-- Section 4.3: the output history of every state of the state graph is a vertex. -/
theorem certified_output_mem {s : State} (hs : Certified s) :
    s.output ∈ Data.historyGraph.map Prod.fst := by
  have h := (certified_windowBound hs).1
  unfold checkStateHistories at h
  exact HistoryGraph.mem_of_lookup_isSome (Bool.and_eq_true_iff.mp h).2

/-- Every entry of the window-bound table passes `checkWindowVertex`. -/
theorem checkWindowVertex_of_lookup {vertex : ℕ} {bound : WindowBound}
    (h : windowBound? vertex = some bound) : checkWindowVertex (vertex, bound) = true :=
  indexedAll_eq_true.mp windowVertices_checked _ (indexedLookup_mem h)

/-- Section 6.6: every vertex of the history graph has window bounds. -/
theorem graphVertex_windowBound {vertex : ℕ} (hv : vertex ∈ Data.historyGraph.map Prod.fst) :
    ∃ bound, windowBound? vertex = some bound := by
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hv
  have h := indexedAll_eq_true.mp graphVertices_checked entry hentry
  exact Option.isSome_iff_exists.mp h

/-- Section 6.6: every vertex of the history graph is the output history of
some state of the state graph. -/
theorem graphVertex_isOutput {vertex : ℕ} (hv : vertex ∈ Data.historyGraph.map Prod.fst) :
    ∃ s, Certified s ∧ s.output = vertex := by
  obtain ⟨bound, hbound⟩ := graphVertex_windowBound hv
  have h := checkWindowVertex_of_lookup hbound
  simp only [checkWindowVertex, Bool.and_eq_true] at h
  obtain ⟨-, hwitness⟩ := h
  cases hs : lookupStateIndex bound.witness Data.stateIndex with
  | none => simp [hs] at hwitness
  | some s =>
    simp only [hs, Option.map_some, beq_iff_eq, Option.some.injEq] at hwitness
    have hmem : s ∈ Data.states.toList := by
      rw [← stateIndex_entries]
      exact List.mem_map.mpr ⟨_, lookupStateIndex_mem hs, rfl⟩
    obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp (by simpa using hmem)
    exact ⟨s, ⟨⟨i, hi⟩, heq⟩, hwitness⟩

/-- **Proposition 24(i).** Every vertex `W` whose last symbol has column bit 1
satisfies `(19√5 - 49) / 8 ≤ lo(W)` and `hi(W) ≤ √5 - 1`. -/
theorem upper_window_bounds {vertex : ℕ} (hv : vertex ∈ Data.historyGraph.map Prod.fst)
    (hupper : upperBit (vertex % 4) = 1) :
    (19 * Real.sqrt 5 - 49) / 8 ≤ windowLo vertex ∧ windowHi vertex ≤ Real.sqrt 5 - 1 := by
  obtain ⟨bound, hbound⟩ := graphVertex_windowBound hv
  have h := checkWindowVertex_of_lookup hbound
  simp only [checkWindowVertex, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    hupper, not_true_eq_false, false_or, decide_eq_true_eq] at h
  obtain ⟨⟨-, hlo, hhi⟩, -⟩ := h
  have hlo' := sqrtFiveEval_le hlo
  have hhi' := sqrtFiveEval_le hhi
  simp only [sqrtFiveEval_apply] at hlo' hhi'
  push_cast at hlo' hhi'
  rw [windowLo_of_lookup hbound, windowHi_of_lookup hbound, sqrtFiveEval_apply,
    sqrtFiveEval_apply]
  constructor <;> linarith

/-- `16 ε(x) = 16 U(x) + 8 x - 8 x √5` as an element of `ℤ√5`. -/
def scaledCountError (count x : ℕ) : ZSqrtFive :=
  ⟨16 * count + 8 * x, -8 * x⟩

/-- The direct check of Proposition 24(c) at column `n`, read from the table
of the first 49 rows. -/
def checkWindowStart (n : ℕ) : Bool :=
  match windowBound? (historyWindow firstSymbol (n - 1)) with
  | some bound =>
      decide (2 * bound.lo ≤ scaledCountError (firstUpperCount (n - 1)) (n - 1) ∧
        scaledCountError (firstUpperCount (n - 1)) (n - 1) ≤ 2 * bound.hi)
  | none => false

/-- Proposition 24(c), checked by kernel reduction for `30 ≤ n ≤ 48`. -/
theorem windowStart_checked : ∀ n : Fin 49, 30 ≤ n.val → checkWindowStart n = true := by
  decide +kernel

/-- A successful direct check supplies window bounds at the window before column
`n` and the two scaled comparisons with `ε(n - 1)`. -/
theorem checkWindowStart_spec {n : ℕ} (h : checkWindowStart n = true) :
    ∃ bound, windowBound? (historyWindow firstSymbol (n - 1)) = some bound ∧
      2 * bound.lo ≤ scaledCountError (firstUpperCount (n - 1)) (n - 1) ∧
      scaledCountError (firstUpperCount (n - 1)) (n - 1) ≤ 2 * bound.hi := by
  unfold checkWindowStart at h
  split at h
  · exact ⟨_, ‹_›, of_decide_eq_true h⟩
  · exact absurd h Bool.false_ne_true

/-- **Proposition 24(c)**, the hypothesis of Lemma 23: for `30 ≤ n ≤ 48`,
`lo(W) ≤ ε(n - 1) ≤ hi(W)` with `W = σ_{n-12} … σ_{n-1}`. -/
theorem window_bounds_start {n : ℕ} (h30 : 30 ≤ n) (h48 : n ≤ 48) :
    windowLo (historyWindow queenSymbol (n - 1)) ≤ countError upperCount (n - 1) ∧
      countError upperCount (n - 1) ≤ windowHi (historyWindow queenSymbol (n - 1)) := by
  have hwindow : historyWindow queenSymbol (n - 1) = historyWindow firstSymbol (n - 1) := by
    unfold historyWindow
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    simp only [historyLength] at hk' ⊢
    exact queenSymbol_eq_firstSymbol (by omega)
  have hcount : countError upperCount (n - 1) =
      (firstUpperCount (n - 1) : ℝ) - (Real.sqrt 5 - 1) / 2 * ((n - 1 : ℕ) : ℝ) := by
    rw [countError, upperCount_eq_firstUpperCount (by omega), inv_goldenRatio_eq]
  obtain ⟨bound, hbound, hlo, hhi⟩ :=
    checkWindowStart_spec (windowStart_checked ⟨n, by omega⟩ h30 : checkWindowStart n = true)
  have hlo' := sqrtFiveEval_le hlo
  have hhi' := sqrtFiveEval_le hhi
  simp only [map_mul, map_ofNat, sqrtFiveEval_apply, scaledCountError] at hlo' hhi'
  push_cast at hlo' hhi'
  rw [hwindow, hcount, windowLo_of_lookup hbound, windowHi_of_lookup hbound, sqrtFiveEval_apply,
    sqrtFiveEval_apply]
  constructor <;> linarith

end Queens.Finite
