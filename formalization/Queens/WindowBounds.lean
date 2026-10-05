import Queens.ErrorIdentity
import Queens.Exactness
import Queens.Finite.FirstColumns
import Queens.Finite.Reachability
import Queens.Finite.WindowBound

/-!
# Window bounds hold on the board

Section 6.6 bounds the counting error `ε(x) = U(x) - x / φ` by numbers attached
to the vertices of the history graph. This file formalizes the link between the
states before columns `n` and `m`, Definition 22 (consistent window bounds), and
Lemma 23 (window bounds hold on the board), for arbitrary real functions `lo`
and `hi`. The finite verification of particular bounds, Proposition 24, is
separate; see `Queens.KnuthRanges`.

## Main statements

* `Queens.input_eq_output_of_represented`: the window link
  `H_in(S_n) = H_out(S_m)`, equation (27).
* `Queens.ConsistentWindowBounds`: **Definition 22**.
* `Queens.window_bounds_hold`: **Lemma 23**.

## Implementation notes

Vertices are encoded twelve-symbol words, so `lo` and `hi` are functions on
`ℕ`; only their values at vertices matter.
-/

namespace Queens

open scoped goldenRatio

/-- Section 6.6: the twelve symbols `σ_{n-12} … σ_{n-1}` before column `n`, encoded. -/
noncomputable def outputWindow (n : ℕ) : ℕ :=
  Finite.historyWindow queenSymbol (n - 1)

/-- **Definition 22 (consistent window bounds).** Real-valued functions `lo` and
`hi` on the vertices of the history graph are consistent if every state `S` of
the state graph satisfies, with `V = H_in(S)` and `W = H_out(S)`,
`lo(W) ≤ Y(S) - hi(V) / φ` and `Y(S) - lo(V) / φ ≤ hi(W)`. -/
def ConsistentWindowBounds (lo hi : ℕ → ℝ) : Prop :=
  ∀ s, Relation.ReflTransGen Finite.Step Finite.initialState s →
    lo s.output ≤ Finite.errorTerm s - hi s.input / φ ∧
      Finite.errorTerm s - lo s.input / φ ≤ hi s.output

/-- Section 6.6: the window bounds hold before column `n`, that is,
`lo(W) ≤ ε(n - 1) ≤ hi(W)` with `W = σ_{n-12} … σ_{n-1}`. -/
def WindowBoundsHold (lo hi : ℕ → ℝ) (n : ℕ) : Prop :=
  lo (outputWindow n) ≤ countError upperCount (n - 1) ∧
    countError upperCount (n - 1) ≤ hi (outputWindow n)

/-- The output history of a state describing the board before column `n` is
the window `σ_{n-12} … σ_{n-1}`. -/
theorem StateRepresented.output_eq_outputWindow {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s) : s.output = outputWindow n := by
  rw [← hrep.output_eq, outputWindow, Finite.historyWindow, wordSegment]
  congr 2

/-- **The window link**, equation (27) of Section 6.6. If states
describe the board before column `n` and before its least unused row `m`, then
`H_in(S_n) = H_out(S_m)`: both are `σ_{m-12} … σ_{m-1}`. -/
theorem input_eq_output_of_represented {n : ℕ} {s t : Finite.State}
    (hs : StateRepresented n s) (ht : StateRepresented (rowReference n) t) :
    s.input = t.output := by
  rw [← hs.input_eq, ← ht.output_eq]

/-- On the board, the error term `Y(S_n)` of the state before column `n` is
`w - |D| + 1 - z / φ` for the actual records. -/
theorem RecordsRepresented.errorTerm_eq {n : ℕ} {s : Finite.State}
    (hrep : RecordsRepresented n s) :
    Finite.errorTerm s =
      (window n : ℝ) - ((diagonalOffsets n).card : ℝ) + 1 - (upperDisplacement n : ℝ) / φ := by
  rw [Finite.errorTerm, hrep.window_eq, hrep.diagonalOffsets_eq, hrep.upperDisplacement_eq]

/-- Section 6.6: before every column `n ≥ 49`, the least unused row `m` satisfies
`30 ≤ m < n`, and the states before columns `n` and `m` describe the board. -/
theorem exists_linked_states {n : ℕ} (hn : 49 ≤ n) :
    30 ≤ rowReference n ∧ rowReference n < n ∧
      ∃ s t, StateRepresented n s ∧ Finite.Certified s ∧
        StateRepresented (rowReference n) t ∧ s.input = t.output := by
  obtain ⟨s, hs, hcert, -⟩ := actualInvariant_of_localStepExact local_step_exact n (by omega)
  have hm := Finite.thirty_le_rowReference hn
  have hcausal := hs.requests_causal (by omega) (Finite.certified_condition hcert)
  obtain ⟨t, ht, -, -⟩ := actualInvariant_of_localStepExact local_step_exact _ hm
  exact ⟨hm, by omega, s, t, hs, hcert, ht, input_eq_output_of_represented hs ht⟩

/-- **Lemma 23 (window bounds hold on the board).** Let `lo` and `hi` be
consistent, and suppose that `lo(W) ≤ ε(n - 1) ≤ hi(W)` with
`W = σ_{n-12} … σ_{n-1}` for `30 ≤ n ≤ 48`. Then the same holds for every
`n ≥ 30`. -/
theorem window_bounds_hold {lo hi : ℕ → ℝ} (hconsistent : ConsistentWindowBounds lo hi)
    (hstart : ∀ n, 30 ≤ n → n ≤ 48 → WindowBoundsHold lo hi n) :
    ∀ n, 30 ≤ n → WindowBoundsHold lo hi n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hdirect : n ≤ 48
    · exact hstart n hn hdirect
    obtain ⟨hm, hmn, s, t, hs, hcert, ht, hlink⟩ := exists_linked_states (n := n) (by omega)
    obtain ⟨hlow, hhigh⟩ := ih _ hmn hm
    rw [← ht.output_eq_outputWindow, ← hlink] at hlow hhigh
    obtain ⟨hconsLow, hconsHigh⟩ :=
      hconsistent s (Finite.certified_iff_reachable.mp hcert)
    rw [hs.errorTerm_eq] at hconsLow hconsHigh
    have hidentity := one_step_error_identity (n := n) (by omega)
    have hphi := Real.goldenRatio_pos
    rw [WindowBoundsHold, ← hs.output_eq_outputWindow]
    constructor
    · calc lo s.output
          ≤ _ - hi s.input / φ := hconsLow
        _ ≤ _ - countError upperCount (rowReference n - 1) / φ := by
          gcongr
        _ = countError upperCount (n - 1) := hidentity.symm
    · calc countError upperCount (n - 1)
          = _ - countError upperCount (rowReference n - 1) / φ := hidentity
        _ ≤ _ - lo s.input / φ := by gcongr
        _ ≤ hi s.output := hconsHigh

end Queens
