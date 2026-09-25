import Queens.Finite.PrefixTransfer
import Queens.LocalRepresentation
import Queens.Finite.History

/-!
# The first thirty queens

Section 6.1 of *Greedy Queens and the Golden Ratio* starts the local calculation
before column 30. The table here is checked against the greedy rule itself:
each listed row is unattacked, and every smaller row is attacked. The uniqueness
of the least available row identifies the table with the actual sequence `q`.
Thus the table is data, not an assumption about the greedy sequence.
-/

namespace Queens.Finite

/-- Section 6.1: the displayed first thirty rows, used as a finite certificate. -/
def seedRows : List ℕ :=
  [0, 2, 4, 1, 3, 8, 10, 12, 14, 5,
   7, 18, 6, 21, 9, 24, 26, 28, 30, 11,
   13, 34, 36, 38, 40, 15, 17, 44, 16, 47]

/-- Section 6.1: read an entry of the finite row certificate. -/
def seedRow (n : ℕ) : ℕ := seedRows[n]?.getD 0

/-- Section 6.1: every listed queen is exactly the least available row against
the earlier entries. The finite check is reduced directly by the Lean kernel. -/
theorem seedRows_greedy : ∀ n : Fin 30,
    Available n.val (seedRow n.val) (fun i => seedRow i.val) ∧
      ∀ r : Fin (seedRow n.val), ¬Available n.val r.val (fun i => seedRow i.val) := by
  decide

/-- Section 6.1: the checked finite table agrees with the actual greedy sequence
in all first thirty columns. No infinite-sequence value is trusted as input. -/
theorem q_eq_seedRow {n : ℕ} (hn : n < 30) : q n = seedRow n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hprev : (fun i : Fin n => q i.val) = fun i => seedRow i.val := by
        funext i
        exact ih i.val i.isLt (by omega)
      have hspec := seedRows_greedy ⟨n, hn⟩
      have hle : q n ≤ seedRow n := by
        apply q_le_of_available
        rw [hprev]
        exact hspec.1
      apply Nat.le_antisymm hle
      by_contra hlt
      have hsmall : q n < seedRow n := by omega
      have havailable := q_available n
      rw [hprev] at havailable
      exact hspec.2 ⟨q n, hsmall⟩ havailable

/-- Definition 9 evaluated on the first thirty columns, independently of the
local calculation. -/
def seedSymbol (n : ℕ) : ℕ :=
  2 * (if n < seedRow n then 1 else 0) +
    if ∃ i : Fin n, i.val < seedRow i.val ∧ seedRow i.val = n then 1 else 0

/-- Section 6.1: the computed finite queen word is the actual queen word. -/
theorem queenSymbol_eq_seedSymbol {n : ℕ} (hn : n < 30) :
    queenSymbol n = seedSymbol n :=
  queenSymbol_eq_of_prefix (fun i hi => q_eq_seedRow (by omega))

/-- Section 6.1: every lower queen in the starting prefix has discrepancy at
most four, measured against its lower-queen rank through the current column. -/
theorem seed_discrepancy : ∀ n : Fin 30, seedRow n.val < n.val →
    |(n.val : ℤ) - seedRow n.val -
      (((Finset.range (n.val + 1)).filter (fun i => seedRow i < i)).card : ℤ)| ≤ 4 := by
  decide

/-- Section 6.1: the finite lower-discrepancy check holds for the actual board. -/
theorem prefix_discrepancy {n : ℕ} (hn : n < 30) (hlower : q n < n) :
    |(n : ℤ) - q n -
      (((Finset.range (n + 1)).filter (fun i => q i < i)).card : ℤ)| ≤ 4 := by
  have hsets : (Finset.range (n + 1)).filter (fun i => q i < i) =
      (Finset.range (n + 1)).filter (fun i => seedRow i < i) := by
    apply Finset.filter_congr
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [q_eq_seedRow (by omega)]
  rw [hsets, q_eq_seedRow hn]
  exact seed_discrepancy ⟨n, hn⟩ (by rwa [← q_eq_seedRow hn])

/-- Section 6.1: occupied rows obtained directly from the checked prefix. -/
theorem occupiedRows_seed : occupiedRows 30 = (Finset.range 30).image seedRow :=
  occupiedRows_eq_of_prefix (fun _ hi => q_eq_seedRow hi)

/-- Section 6.1: the lower columns obtained directly from the checked prefix. -/
theorem earlierLowerColumns_seed : earlierLowerColumns 30 =
    (Finset.range 30).filter (fun i => seedRow i < i) :=
  earlierLowerColumns_eq_of_prefix (fun _ hi => q_eq_seedRow hi)

/-- Section 6.1: used lower diagonals obtained directly from the checked prefix. -/
theorem lowerDiagonals_seed : lowerDiagonals 30 =
    ((Finset.range 30).filter (fun i => seedRow i < i)).image (fun i => i - seedRow i) :=
  lowerDiagonals_eq_of_prefix (fun _ hi => q_eq_seedRow hi)

/-- Section 6.1: the actual least unused row before column 30 is 19. -/
theorem rowReference_thirty : rowReference 30 = 19 := by
  unfold rowReference
  rw [occupiedRows_seed]
  apply leastUnused_eq_of_spec
  · decide
  · have hfinite : ∀ r : Fin 19, r.val ∈ (Finset.range 30).image seedRow := by decide
    intro r hr
    exact hfinite ⟨r, hr⟩

/-- Section 6.1: the actual least unused positive lower diagonal is 11. -/
theorem diagonalReference_thirty : diagonalReference 30 = 11 := by
  unfold diagonalReference
  rw [lowerDiagonals_seed]
  apply leastUnused_eq_of_spec
  · decide
  · have hfinite : ∀ r : Fin 11, r.val ∈ insert 0
        (((Finset.range 30).filter (fun i => seedRow i < i)).image
          (fun i => i - seedRow i)) := by decide
    intro r hr
    exact hfinite ⟨r, hr⟩

/-- Section 6.1: the actual upper-count reference before column 30 is 12. -/
theorem countReference_thirty : countReference 30 = 12 := by
  unfold countReference
  rw [rowReference_thirty]
  rw [upperCount_eq_of_prefix (rows := seedRow) (n := 18)
    (fun i hi => q_eq_seedRow (by omega))]
  decide

/-- Section 6.1: the actual window record is the displayed initial value. -/
theorem window_thirty : window 30 = initialState.w := by
  simp [window, rowReference_thirty, diagonalReference_thirty, initialState]

/-- Section 6.1: the actual upper displacement is the displayed initial value. -/
theorem upperDisplacement_thirty : upperDisplacement 30 = initialState.z := by
  simp [upperDisplacement, rowReference_thirty, countReference_thirty, initialState]

/-- Section 6.1: the actual row record before column 30 is empty. -/
theorem rowOffsets_thirty : rowOffsets 30 = offsets initialState.R := by
  rw [rowOffsets_eq_of_prefix (rows := seedRow) (n := 30)
    (fun i hi => q_eq_seedRow hi), rowReference_thirty]
  decide

/-- Section 6.1: the actual diagonal record before column 30 consists of offset one. -/
theorem diagonalOffsets_thirty : diagonalOffsets 30 = offsets initialState.D := by
  unfold diagonalOffsets
  rw [lowerDiagonals_seed, diagonalReference_thirty]
  decide

/-- Section 6.1: the actual antidiagonal record before column 30 is empty. -/
theorem antidiagonalOffsets_thirty : antidiagonalOffsets 30 = offsets initialState.A := by
  rw [antidiagonalOffsets_eq_of_prefix (rows := seedRow) (n := 30)
    (fun i hi => q_eq_seedRow hi), rowReference_thirty]
  decide

/-- Section 6.1: a word segment computed from the finite seed table. -/
def seedSegment (start length : ℕ) : List ℕ :=
  (List.range length).map (fun k => seedSymbol (start + k))

/-- Section 6.1: finite seed segments are actual queen-word segments whenever
all their indices belong to the verified thirty-column prefix. -/
theorem wordSegment_eq_seedSegment {start length : ℕ} (h : start + length ≤ 30) :
    wordSegment start length = seedSegment start length := by
  unfold wordSegment seedSegment
  apply List.map_congr_left
  intro i hi
  exact queenSymbol_eq_seedSymbol (by have := List.mem_range.mp hi; omega)

/-- Section 6.1: all eight displayed records, including the three word fields,
represent the actual board before column 30. -/
theorem initialState_represented : StateRepresented 30 initialState where
  window_eq := window_thirty
  upperDisplacement_eq := upperDisplacement_thirty
  rowOffsets_eq := rowOffsets_thirty
  diagonalOffsets_eq := diagonalOffsets_thirty
  antidiagonalOffsets_eq := antidiagonalOffsets_thirty
  history_start := by rw [rowReference_thirty]; decide
  input_eq := by
    rw [rowReference_thirty]
    rw [wordSegment_eq_seedSegment (by decide)]
    decide
  queue_eq := by
    rw [rowReference_thirty]
    rw [wordSegment_eq_seedSegment (by decide)]
    decide
  output_eq := by
    rw [wordSegment_eq_seedSegment (by decide)]
    decide
  queue_nonempty := by decide
  queue_before_column := by rw [rowReference_thirty]; decide

/-- Section 6.1: the seed word follows the checked history graph. -/
theorem seedWord_follows : Data.historyGraph.FollowsThrough seedSymbol 29 := by
  have hcheck : ∀ t : Fin 30, historyLength ≤ t.val →
      (Data.historyGraph.lookup (historyWindow seedSymbol t.val)).isSome = true ∧
        (t.val < 29 →
          ((Data.historyGraph.answers (historyWindow seedSymbol t.val)).getD []).contains
          (seedSymbol (t.val + 1)) = true) := by
    decide +kernel
  intro t ht
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ht
  have h := hcheck ⟨t, by omega⟩ hlo
  exact ⟨HistoryGraph.mem_of_lookup_isSome h.1, h.2⟩

/-- Section 6.1: the actual queen word through column 29 follows the graph,
so the initial input and output histories are grounded in the greedy board. -/
theorem queenWord_follows_through_twentyNine :
    Data.historyGraph.FollowsThrough queenSymbol 29 := by
  intro t ht
  have ht' := Finset.mem_Icc.mp ht
  have hw : historyWindow queenSymbol t = historyWindow seedSymbol t := by
    apply congrArg encode
    exact wordSegment_eq_seedSegment (by dsimp [historyLength] at ht' ⊢; omega)
  have hs := seedWord_follows t ht
  rw [hw]
  refine ⟨hs.1, ?_⟩
  intro hlt
  rw [queenSymbol_eq_seedSymbol (by omega)]
  exact hs.2 hlt

end Queens.Finite
