import Queens.Finite.Encoding
import Queens.Finite.MaskSemantics
import Queens.LocalRequests

/-!
# The record update reproduces the actual board update

This file proves the last stage of Lemma 16, using the mathematical reference
updates from Section 4.5 and the exact bit-mask and word encodings. Its hypotheses
explicitly identify the selected queen and reference advances; choosing that
queen and finding those advances are separate stages of Algorithm 1.
-/

namespace Queens.Finite

/-- Section 4.5: recording the actual queen produces the actual three temporary
sets. The lower-diagonal insertion uses signed arithmetic before conversion to
its nonnegative offset. -/
theorem inserted_masks_represented {n : ℕ} {s : State}
    (hrep : RecordsRepresented n s) {choice : Option ℕ}
    (hchoice : choice = if q n < n then some (rowOffset n) else none) :
    insertedRowOffsets n = offsets (choice.elim s.R (insertOffset s.R)) ∧
    insertedDiagonalOffsets n = offsets
      (choice.elim s.D (fun r => insertOffset s.D (s.w - r).toNat)) ∧
    insertedAntidiagonalOffsets n = offsets (choice.elim s.A (insertOffset s.A)) := by
  subst choice
  by_cases hn : q n < n
  · have hdiag : (s.w - rowOffset n).toNat = n - q n - diagonalReference n := by
      have hm := rowReference_le_q n
      have hd := diagonalReference_le_lowerDiagonal hn
      rw [← hrep.window_eq]
      unfold window rowOffset
      omega
    simp only [if_pos hn, Option.elim_some, offsets_insertOffset, hdiag,
      insertedRowOffsets, insertedDiagonalOffsets, insertedAntidiagonalOffsets]
    simp only [hrep.rowOffsets_eq, hrep.diagonalOffsets_eq,
      hrep.antidiagonalOffsets_eq, and_self]
  · simp only [if_neg hn, Option.elim_none, insertedRowOffsets,
      insertedDiagonalOffsets, insertedAntidiagonalOffsets]
    simp only [hrep.rowOffsets_eq, hrep.diagonalOffsets_eq,
      hrep.antidiagonalOffsets_eq, and_self]

/-- Section 4.5: once the temporary diagonal mask represents the actual set,
the executable least-absent-bit search finds exactly the actual advance `ν`. -/
theorem diagonalAdvance_actual {n mask : ℕ}
    (hmask : insertedDiagonalOffsets n = offsets mask) :
    diagonalAdvance mask = lowerDiagonalAdvance n := by
  have hs := diagonalAdvance_spec mask
  have hfree := lowerDiagonalAdvance_free n
  rw [hmask] at hfree
  apply Nat.le_antisymm
  · by_contra h
    exact hfree (hs.2 _ (by omega))
  · by_contra h
    have hm := lowerDiagonalAdvance_minimal
      (by omega : diagonalAdvance mask < lowerDiagonalAdvance n)
    rw [hmask] at hm
    exact hs.1 hm

/-- Equation (update): correctly represented temporary records, actual advances,
and actual consumed symbols yield all five actual numerical/set records. -/
theorem updateState_records {n : ℕ} {s : State}
    (hn : 0 < n) (hrep : RecordsRepresented n s)
    {rows diagonals antidiagonals : ℕ} {queue : List ℕ} (symbol : ℕ)
    (hrows : insertedRowOffsets n = offsets rows)
    (hdiagonals : insertedDiagonalOffsets n = offsets diagonals)
    (hantidiagonals : insertedAntidiagonalOffsets n = offsets antidiagonals)
    (hconsumed : queue.take (rowAdvance n) = wordSegment (rowReference n) (rowAdvance n))
    (memory : ℕ := historyLength) :
    RecordsRepresented (n + 1)
      (updateState s rows diagonals antidiagonals (lowerDiagonalAdvance n)
        (rowAdvance n) queue symbol (memory := memory)) where
  window_eq := by
    simpa only [updateState, hrep.window_eq] using window_succ n
  upperDisplacement_eq := by
    simpa only [updateState, hrep.upperDisplacement_eq, hconsumed]
      using upperDisplacement_succ_word hn
  rowOffsets_eq := by
    simpa only [updateState, offsets_shiftRight, hrows] using rowOffsets_succ n
  diagonalOffsets_eq := by
    simpa only [updateState, offsets_shiftRight, hdiagonals] using diagonalOffsets_succ n
  antidiagonalOffsets_eq := by
    simpa only [updateState, offsets_shiftRight, hantidiagonals] using antidiagonalOffsets_succ n

/-- Lemma 16(ii), final update stage: actual temporary records, advances, and
symbols produce a completely represented state at the next column. The strict
queue bound records that the row-search stopping bit remains in the queue. -/
theorem updateState_represented {memory n : ℕ} {s : State}
    (hn : 0 < n) (hrep : StateRepresented n s (memory := memory))
    {rows diagonals antidiagonals : ℕ} {queue : List ℕ} {symbol : ℕ}
    (hrows : insertedRowOffsets n = offsets rows)
    (hdiagonals : insertedDiagonalOffsets n = offsets diagonals)
    (hantidiagonals : insertedAntidiagonalOffsets n = offsets antidiagonals)
    (hqueue : wordSegment (rowReference n) queue.length = queue)
    (hmu : rowAdvance n < queue.length)
    (hbefore : rowReference n + queue.length ≤ n)
    (hsymbol : symbol = queenSymbol n) :
    StateRepresented (n + 1)
      (updateState s rows diagonals antidiagonals (lowerDiagonalAdvance n)
        (rowAdvance n) queue symbol (memory := memory)) (memory := memory) := by
  have hconsumed : queue.take (rowAdvance n) =
      wordSegment (rowReference n) (rowAdvance n) := by
    calc
      queue.take (rowAdvance n) =
          (wordSegment (rowReference n) queue.length).take (rowAdvance n) :=
        congrArg (fun word => word.take (rowAdvance n)) hqueue.symm
      _ = wordSegment (rowReference n) (rowAdvance n) :=
        wordSegment_take _ _ _ (by omega)
  refine
    { toRecordsRepresented := updateState_records hn hrep.toRecordsRepresented symbol
        hrows hdiagonals hantidiagonals hconsumed (memory := memory)
      history_start := ?_
      input_eq := ?_
      queue_eq := ?_
      output_eq := ?_
      queue_nonempty := ?_
      queue_before_column := ?_ }
  · have hmono := rowReference_mono (show n ≤ n + 1 by omega)
    exact hrep.history_start.trans hmono
  · change inputHistoryAt (rowReference (n + 1)) (memory := memory) =
      (queue.take (rowAdvance n)).foldl (destination (memory := memory)) s.input
    rw [hconsumed, ← hrep.input_eq]
    change inputHistoryAt (rowReference (n + 1)) (memory := memory) =
      (wordSegment (rowReference n) (rowAdvance n)).foldl (destination (memory := memory))
        (inputHistoryAt (rowReference n) (memory := memory))
    rw [fold_destination_wordSegment _ _ hrep.history_start, rowReference_add_advance]
  · have hdrop := wordSegment_drop (rowReference n) queue.length (rowAdvance n) (by omega)
    rw [hqueue, rowReference_add_advance] at hdrop
    simpa only [updateState, List.length_drop] using hdrop.symm
  · change inputHistoryAt (n + 1) (memory := memory) =
      destination s.output symbol (memory := memory)
    have hout : inputHistoryAt n (memory := memory) = s.output := hrep.output_eq
    rw [← hout, hsymbol, destination_inputHistoryAt]
    have hh := hrep.history_start
    omega
  · change 0 < (queue.drop (rowAdvance n)).length
    rw [List.length_drop]
    omega
  · change rowReference (n + 1) + (queue.drop (rowAdvance n)).length ≤ n + 1
    rw [List.length_drop]
    have href := rowReference_add_advance n
    omega

end Queens.Finite
