import Queens.Finite.RunWitnessData
import Queens.Finite.PrefixTransfer
import Queens.LocalRepresentation
import Queens.Finite.FortyData
import Queens.Finite.HistoryPathChecking

/-!
# The forty-symbol starting board

Corollary 19 (Section 6.5) starts the forty-symbol verification immediately
before column 80. All numerical and word records are computed from the already
checked greedy witness prefix. The separate history-path check establishes that
the earlier queen word follows the forty-symbol graph.
-/

namespace Queens.Finite.Forty

set_option maxRecDepth 100000

/-- Corollary 19: the first eighty proposed rows, taken from the reproducible
witness data and checked independently of the longer attainment prefix. -/
def seedRows : List ℕ := runWitnessRows.take 80

/-- Corollary 19: the proposed row in the eighty-column starting prefix. -/
def seedRow (n : ℕ) : ℕ := seedRows[n]?.getD 0

/-- Corollary 19: kernel verification of precisely the eighty-column seed,
using the proved bitboard implementation of the defining greedy rule. -/
theorem seedRows_checked :
    seedRows.length = 80 ∧ AttackBoard.empty.checkRows seedRows = true := by
  decide +kernel

/-- Corollary 19: the eighty-column starting prefix agrees with the actual
sequence, by the checked defining greedy rule. -/
theorem q_eq_seedRow {n : ℕ} (hn : n < 80) : q n = seedRow n := by
  have hn' : n < seedRows.length := by rw [seedRows_checked.1]; exact hn
  have h := AttackBoard.empty_represents.q_eq_of_checkRows seedRows_checked.2 ⟨n, hn'⟩
  simpa [seedRow, List.getElem?_eq_getElem hn'] using h

/-- Definition 9 evaluated on the first eighty columns, independently of the
local calculation. -/
def seedSymbol (n : ℕ) : ℕ :=
  2 * (if n < seedRow n then 1 else 0) +
    if ∃ i : Fin n, i.val < seedRow i.val ∧ seedRow i.val = n then 1 else 0

/-- Corollary 19, Section 6.5: the computed finite queen word is the actual queen word. -/
theorem queenSymbol_eq_seedSymbol {n : ℕ} (hn : n < 80) :
    queenSymbol n = seedSymbol n :=
  queenSymbol_eq_of_prefix (fun i hi => q_eq_seedRow (by omega))

/-- Corollary 19, Section 6.5: occupied rows obtained directly from the checked prefix. -/
theorem occupiedRows_seed : occupiedRows 80 = (Finset.range 80).image seedRow :=
  occupiedRows_eq_of_prefix (fun _ hi => q_eq_seedRow hi)

/-- Corollary 19, Section 6.5: the lower columns obtained directly from the checked prefix. -/
theorem earlierLowerColumns_seed : earlierLowerColumns 80 =
    (Finset.range 80).filter (fun i => seedRow i < i) :=
  earlierLowerColumns_eq_of_prefix (fun _ hi => q_eq_seedRow hi)

/-- Corollary 19, Section 6.5: used lower diagonals obtained directly from the checked prefix. -/
theorem lowerDiagonals_seed : lowerDiagonals 80 =
    ((Finset.range 80).filter (fun i => seedRow i < i)).image (fun i => i - seedRow i) :=
  lowerDiagonals_eq_of_prefix (fun _ hi => q_eq_seedRow hi)

/-- Corollary 19, Section 6.5: the actual least unused row before column 80 is 51. -/
theorem rowReference_eighty : rowReference 80 = 51 := by
  unfold rowReference
  rw [occupiedRows_seed]
  apply leastUnused_eq_of_spec
  · decide
  · have hfinite : ∀ r : Fin 51, r.val ∈ (Finset.range 80).image seedRow := by decide
    intro r hr
    exact hfinite ⟨r, hr⟩

/-- Corollary 19, Section 6.5: the actual least unused positive lower diagonal is 32. -/
theorem diagonalReference_eighty : diagonalReference 80 = 32 := by
  unfold diagonalReference
  rw [lowerDiagonals_seed]
  apply leastUnused_eq_of_spec
  · decide
  · have hfinite : ∀ r : Fin 32, r.val ∈ insert 0
        (((Finset.range 80).filter (fun i => seedRow i < i)).image
          (fun i => i - seedRow i)) := by decide
    intro r hr
    exact hfinite ⟨r, hr⟩

/-- Corollary 19, Section 6.5: the actual upper-count reference before column 80 is 31. -/
theorem countReference_eighty : countReference 80 = 31 := by
  unfold countReference
  rw [rowReference_eighty]
  rw [upperCount_eq_of_prefix (rows := seedRow) (n := 50)
    (fun i hi => q_eq_seedRow (by omega))]
  decide

/-- Corollary 19, Section 6.5: the actual window record is the displayed initial value. -/
theorem window_eighty : window 80 = FortyData.initialState.w := by
  simp [window, rowReference_eighty, diagonalReference_eighty, FortyData.initialState]

/-- Corollary 19, Section 6.5: the actual upper displacement is the displayed initial value. -/
theorem upperDisplacement_eighty : upperDisplacement 80 = FortyData.initialState.z := by
  simp [upperDisplacement, rowReference_eighty, countReference_eighty, FortyData.initialState]

/-- Corollary 19, Section 6.5: the actual row record before column 80 is empty. -/
theorem rowOffsets_eighty : rowOffsets 80 = offsets FortyData.initialState.R := by
  rw [rowOffsets_eq_of_prefix (rows := seedRow) (n := 80)
    (fun i hi => q_eq_seedRow hi), rowReference_eighty]
  decide

/-- Corollary 19, Section 6.5: the actual diagonal record before column 80 is empty. -/
theorem diagonalOffsets_eighty : diagonalOffsets 80 = offsets FortyData.initialState.D := by
  unfold diagonalOffsets
  rw [lowerDiagonals_seed, diagonalReference_eighty]
  decide

/-- Corollary 19, Section 6.5: the actual antidiagonal record before column 80 is empty. -/
theorem antidiagonalOffsets_eighty : antidiagonalOffsets 80 = offsets FortyData.initialState.A := by
  rw [antidiagonalOffsets_eq_of_prefix (rows := seedRow) (n := 80)
    (fun i hi => q_eq_seedRow hi), rowReference_eighty]
  decide

/-- Corollary 19, Section 6.5: a word segment computed from the finite seed table. -/
def seedSegment (start length : ℕ) : List ℕ :=
  (List.range length).map (fun k => seedSymbol (start + k))

/-- Corollary 19, Section 6.5: finite seed segments are actual queen-word segments whenever
all their indices belong to the verified eighty-column prefix. -/
theorem wordSegment_eq_seedSegment {start length : ℕ} (h : start + length ≤ 80) :
    wordSegment start length = seedSegment start length := by
  unfold wordSegment seedSegment
  apply List.map_congr_left
  intro i hi
  exact queenSymbol_eq_seedSymbol (by have := List.mem_range.mp hi; omega)

/-- Corollary 19, Section 6.5: all eight displayed records, including the three word fields,
represent the actual board before column 80. -/
theorem initialState_represented : StateRepresented 80 FortyData.initialState 40 where
  window_eq := window_eighty
  upperDisplacement_eq := upperDisplacement_eighty
  rowOffsets_eq := rowOffsets_eighty
  diagonalOffsets_eq := diagonalOffsets_eighty
  antidiagonalOffsets_eq := antidiagonalOffsets_eighty
  history_start := by rw [rowReference_eighty]; decide
  input_eq := by
    rw [rowReference_eighty]
    rw [wordSegment_eq_seedSegment (by decide)]
    decide
  queue_eq := by
    rw [rowReference_eighty]
    rw [wordSegment_eq_seedSegment (by decide)]
    decide
  output_eq := by
    rw [wordSegment_eq_seedSegment (by decide)]
    decide
  queue_nonempty := by decide
  queue_before_column := by rw [rowReference_eighty]; decide

/-- Corollary 19, Section 6.5: the seed word follows the checked history graph. -/
theorem seedWord_follows : FortyData.historyGraph.FollowsThrough seedSymbol 79 40 := by
  exact HistoryGraph.checkFollowsThrough_sound (by decide +kernel)

/-- Corollary 19, Section 6.5: the actual queen word through column 79 follows the graph,
so the initial input and output histories are grounded in the greedy board. -/
theorem queenWord_follows_through_seventyNine :
    FortyData.historyGraph.FollowsThrough queenSymbol 79 40 := by
  intro t ht
  have ht' := Finset.mem_Icc.mp ht
  have hw : historyWindow queenSymbol t 40 = historyWindow seedSymbol t 40 := by
    apply congrArg encode
    exact wordSegment_eq_seedSegment (by omega)
  have hs := seedWord_follows t ht
  rw [hw]
  refine ⟨hs.1, ?_⟩
  intro hlt
  rw [queenSymbol_eq_seedSymbol (by omega)]
  exact hs.2 hlt

end Queens.Finite.Forty
