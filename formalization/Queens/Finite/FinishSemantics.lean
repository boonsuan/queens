import Queens.LocalBounds
import Queens.LocalSources
import Queens.Finite.UpdateSemantics

/-!
# Completing the actual local step

After the actual queen choice is known, the output-symbol check and reference
searches of Algorithm 1 produce the actual successor state. The checked output
edge extends the actual queen word's path in the history graph.
-/

namespace Queens.Finite

/-- An allowed four-symbol label occurs in the graph's answer list. -/
theorem HistoryGraph.answer_contains {graph : HistoryGraph} {vertex mask symbol : ℕ}
    (hlookup : graph.lookup vertex = some mask) (hsymbol : symbol < 4)
    (hallowed : hasOffset mask symbol = true) :
    ((graph.answers vertex).getD []).contains symbol = true := by
  simp [HistoryGraph.answers, hlookup, List.mem_filter, hsymbol, hallowed]

/-- A checked next-symbol edge extends the actual word's verified graph path. -/
theorem HistoryGraph.followsThrough_succ {memory : ℕ} {graph : HistoryGraph} {n mask : ℕ}
    (hgraph : graph.WellFormed (memory := memory)) (hn : memory < n)
    (hprevious : graph.FollowsThrough queenSymbol (n - 1) (memory := memory))
    (hlookup : graph.lookup (inputHistoryAt n (memory := memory)) = some mask)
    (hallowed : hasOffset mask (queenSymbol n) = true) :
    graph.FollowsThrough queenSymbol n (memory := memory) := by
  have hentry := HistoryGraph.lookup_mem hlookup
  have hnew := (hgraph.2 _ hentry).2.2 ⟨queenSymbol n, queenSymbol_lt_four n⟩ hallowed
  rw [destination_inputHistoryAt n (by omega)] at hnew
  intro t ht
  have ht' := Finset.mem_Icc.mp ht
  by_cases htn : t < n
  · have hold := hprevious t (Finset.mem_Icc.mpr ⟨ht'.1, by omega⟩)
    refine ⟨hold.1, fun _ => ?_⟩
    by_cases heq : t = n - 1
    · subst t
      rw [historyWindow_previous (by omega), Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact HistoryGraph.answer_contains hlookup (queenSymbol_lt_four n) hallowed
    · exact hold.2 (by omega)
  · have heq : t = n := by omega
    subst t
    exact ⟨hnew, fun h => False.elim (by omega)⟩

/-- The symbol formed from the actual upper/lower choice and the actual row
bit is exactly Definition 9's queen-word symbol. -/
theorem choice_symbol_eq {n : ℕ} (hn : 0 < n) {choice : Option ℕ}
    (hchoice : choice = if q n < n then some (rowOffset n) else none) :
    (if choice.isSome then 0 else 2) + upperRowBit n = queenSymbol n := by
  subst choice
  unfold queenSymbol columnBit
  by_cases hlower : q n < n
  · have hupper : ¬ n < q n := by omega
    simp [hlower, hupper]
  · have hupper : n < q n := by have hne := q_ne_self hn; omega
    simp [hlower, hupper]

/-- A successful finish of the actual queen choice contains the actual next
state and extends the verified queen-word path. This is the final operational
part of Section 5, Lemma 16, generalized to any memory of at least twelve symbols
for the forty-symbol construction of Corollary 19. The geometric count bound
remains twelve, independently of the larger memory. -/
theorem finishChoice_contains_actual_of_extensions_general {memory : ℕ}
    {graph : HistoryGraph} {n length : ℕ} {s : State} {choice : Option ℕ}
    {out : List State} (hmemory : 12 ≤ memory) (hstart : memory < rowReference n)
    (hcount : 12 ≤ countReference n) (hrep : StateRepresented n s (memory := memory))
    (hc : Condition s) (hword : graph.FollowsThrough queenSymbol (n - 1) (memory := memory))
    (hgraph : graph.WellFormed (memory := memory))
    (hextends : ExtendsActualWord graph s.input (rowReference n) (n - rowReference n)
      (memory := memory))
    (hchoice : choice = if q n < n then some (rowOffset n) else none)
    (hlength : length ≤ n - rowReference n) (hzlength : s.z ≤ (length : ℤ))
    (hok : finishChoice graph s (choice, wordSegment (rowReference n) length)
      (memory := memory) = .ok out) :
    ∃ t ∈ out, StateRepresented (n + 1) t (memory := memory) ∧
      graph.FollowsThrough queenSymbol n (memory := memory) := by
  have hnpos : 0 < n := by have := hrep.queue_before_column; omega
  have hm : rowReference n ≤ n := by have := hrep.queue_before_column; omega
  have hbit := hrep.adjustment_difference_eq_upperRowBit hnpos
    (by rw [hrep.upperDisplacement_eq]; exact hc.2.1)
    (by rw [hrep.upperDisplacement_eq]; exact hzlength) (hmemory := hmemory)
  have hbitbound := upperRowBit_le_one n
  have hvalid : ¬ ((upperRowBit n : ℤ) < 0 ∨ 1 < (upperRowBit n : ℤ)) := by omega
  have hsymbol := choice_symbol_eq hnpos hchoice
  have hmasks := inserted_masks_represented hrep.toRecordsRepresented hchoice
  let rows := choice.elim s.R (insertOffset s.R)
  let diagonals := choice.elim s.D (fun r => insertOffset s.D (s.w - r).toNat)
  let antidiagonals := choice.elim s.A (insertOffset s.A)
  have hnu : diagonalAdvance diagonals = lowerDiagonalAdvance n := diagonalAdvance_actual hmasks.2.1
  unfold finishChoice at hok
  simp only [hbit, if_neg hvalid, Int.toNat_natCast, hsymbol] at hok
  cases hlookup : graph.lookup s.output with
  | none =>
    simp only [hlookup] at hok
    change (Except.error Failure.missingOutputEdge : Except Failure (List State)) = .ok out at hok
    cases hok
  | some mask =>
    have hallowed : hasOffset mask (queenSymbol n) = true := by
      by_contra h
      have hfalse : hasOffset mask (queenSymbol n) = false := by simpa using h
      simp only [hlookup, hfalse, Bool.not_false, if_true] at hok
      change (Except.error Failure.missingOutputEdge : Except Failure (List State)) = .ok out at hok
      cases hok
    have hword' : graph.FollowsThrough queenSymbol n (memory := memory) := by
      have hout : inputHistoryAt n (memory := memory) = s.output := hrep.output_eq
      apply HistoryGraph.followsThrough_succ hgraph (by omega) hword
      · rwa [hout]
      · exact hallowed
    simp only [hlookup, hallowed, Bool.not_true, Bool.false_eq_true, if_false] at hok
    change (findFreeRow graph s.input rows 8 0
      (wordSegment (rowReference n) length) (memory := memory) >>= fun advances =>
      pure (advances.map (fun (mu, queue) =>
        updateState s rows diagonals antidiagonals (diagonalAdvance diagonals) mu queue
          (queenSymbol n) (memory := memory)))) = .ok out at hok
    cases hsearch : findFreeRow graph s.input rows 8 0
        (wordSegment (rowReference n) length) (memory := memory) with
    | error e =>
      rw [hsearch] at hok
      change (Except.error e : Except Failure (List State)) = .ok out at hok
      cases hok
    | ok advances =>
      have hout : advances.map (fun (mu, queue) =>
          updateState s rows diagonals antidiagonals (lowerDiagonalAdvance n) mu queue
            (queenSymbol n) (memory := memory)) = out := by
        rw [hsearch] at hok
        change Except.ok (advances.map (fun (mu, queue) =>
          updateState s rows diagonals antidiagonals (diagonalAdvance diagonals) mu queue
            (queenSymbol n) (memory := memory))) = Except.ok out at hok
        have h := Except.ok.inj hok
        rwa [hnu] at h
      have hw : window n ≤ 4 := by rw [hrep.window_eq]; exact hc.1
      have hR : rowOffsets n ⊆ Finset.Icc 1 4 := by
        rw [hrep.rowOffsets_eq]; exact hc.offsets_subset.1
      have hcausal := hrep.requests_causal_general hcount hc
      have hmu := rowAdvance_le_six hw hR
      have hfree := rowAdvance_free hnpos hw hR hcausal
      have hfreeMask : hasOffset rows (rowAdvance n) = false := by
        have hnot : hasOffset rows (rowAdvance n) ≠ true := by
          intro h
          apply hfree.1
          rw [hmasks.1]
          exact mem_offsets.mpr h
        simpa using hnot
      have hblocked : ∀ r < rowAdvance n,
          hasOffset rows r = true ∨ upperRowBit (rowReference n + r) = 1 := by
        intro r hr
        rcases rowAdvance_minimal hnpos hw hR hcausal hr with hmem | hbit
        · left
          apply mem_offsets.mp
          rwa [← hmasks.1]
        · exact Or.inr hbit
      obtain ⟨length', hlength', hmulength', hlimit', hmem⟩ :=
        findFreeRow_contains_actual hextends
          ⟨hfreeMask, hfree.2⟩ hblocked (by omega) (by omega) (by omega) hlength hsearch
      let successor := updateState s rows diagonals antidiagonals (lowerDiagonalAdvance n)
        (rowAdvance n) (wordSegment (rowReference n) length') (queenSymbol n) (memory := memory)
      refine ⟨successor, ?_, ?_, hword'⟩
      · rw [← hout]
        exact List.mem_map.mpr ⟨(rowAdvance n, wordSegment (rowReference n) length'), hmem, rfl⟩
      · apply updateState_represented hnpos hrep hmasks.1 hmasks.2.1 hmasks.2.2
        · simp
        · simp only [wordSegment_length]
          omega
        · simp only [wordSegment_length]
          omega
        · rfl

/-- The finishing stage specialized to twelve-symbol histories after column
30. This wrapper supplies the numerical starting bounds used in Lemma 16. -/
theorem finishChoice_contains_actual_of_extensions {graph : HistoryGraph}
    {n length : ℕ} {s : State} {choice : Option ℕ} {out : List State}
    (hn : 30 ≤ n) (hrep : StateRepresented n s) (hc : Condition s)
    (hword : graph.FollowsThrough queenSymbol (n - 1)) (hgraph : graph.WellFormed)
    (hextends : ExtendsActualWord graph s.input (rowReference n) (n - rowReference n))
    (hchoice : choice = if q n < n then some (rowOffset n) else none)
    (hlength : length ≤ n - rowReference n) (hzlength : s.z ≤ (length : ℤ))
    (hok : finishChoice graph s (choice, wordSegment (rowReference n) length) = .ok out) :
    ∃ t ∈ out, StateRepresented (n + 1) t ∧ graph.FollowsThrough queenSymbol n := by
  have hm := rowReference_ge_nineteen hn
  exact finishChoice_contains_actual_of_extensions_general (by decide)
    (by dsimp [historyLength]; omega)
    (countReference_ge_twelve hn) hrep hc hword hgraph hextends hchoice hlength hzlength hok

/-- The actual finish stage for the paper's checked history graph. Its
well-formedness and the actual-word extension hypothesis have both been proved. -/
theorem finishChoice_contains_actual {n length : ℕ} {s : State} {choice : Option ℕ}
    {out : List State} (hn : 30 ≤ n) (hrep : StateRepresented n s)
    (hc : Condition s) (hword : Data.historyGraph.FollowsThrough queenSymbol (n - 1))
    (hchoice : choice = if q n < n then some (rowOffset n) else none)
    (hlength : length ≤ n - rowReference n) (hzlength : s.z ≤ (length : ℤ))
    (hok : finishChoice Data.historyGraph s
      (choice, wordSegment (rowReference n) length) = .ok out) :
    ∃ t ∈ out, StateRepresented (n + 1) t ∧ Data.historyGraph.FollowsThrough queenSymbol n :=
  finishChoice_contains_actual_of_extensions hn hrep hc hword historyGraph_wellFormed
    (hrep.extendsActualWord hn hword) hchoice hlength hzlength hok

end Queens.Finite
