import Queens.LocalRepresentation
import Queens.Finite.HistoryCore
import Queens.Finite.Encoding
import Queens.Finite.Branching

/-!
# Requests along the actual queen word

Lemma 16 answers requests with already determined symbols. The history graph
admits these answers because the earlier actual word follows the graph. This file
connects that mathematical fact to the executable `extendBy` and `extendQueue`.
-/

namespace Queens

/-- Every symbol in an actual word segment lies in the four-symbol alphabet
(Definition 9). -/
theorem wordSegment_symbols_lt_four (start length : ℕ) :
    ∀ symbol ∈ wordSegment start length, symbol < 4 := by
  intro symbol hsymbol
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hsymbol
  exact queenSymbol_lt_four _

/-- The encoded history immediately before an absolute input position.
This is the input vertex used for requests in Section 4.3. -/
noncomputable def inputHistoryAt (start : ℕ) (memory : ℕ := Finite.historyLength) : ℕ :=
  Finite.encode (wordSegment (start - memory) memory)

/-- Appending an actual word segment advances its encoded history to the
end of that segment, keeping the last `memory` symbols (Section 4.5). -/
theorem fold_destination_wordSegment {memory : ℕ} (start length : ℕ)
    (hstart : memory ≤ start) :
    (wordSegment start length).foldl (Finite.destination (memory := memory))
        (inputHistoryAt (memory := memory) start) =
      inputHistoryAt (memory := memory) (start + length) := by
  unfold inputHistoryAt
  rw [Finite.foldl_destination_encode (wordSegment_length _ _)
    (wordSegment_symbols_lt_four _ _) (wordSegment_symbols_lt_four _ _)]
  have hconcat := wordSegment_add (start - memory) memory length
  rw [Nat.sub_add_cancel hstart] at hconcat
  rw [← hconcat, wordSegment_length,
    wordSegment_drop _ _ _ (by omega)]
  congr 2 <;> omega

/-- Advancing one actual symbol shifts the preceding history
to the next input position (Section 4.3). -/
theorem destination_inputHistoryAt {memory : ℕ} (start : ℕ) (hstart : memory ≤ start) :
    Finite.destination (memory := memory) (inputHistoryAt (memory := memory) start)
        (queenSymbol start) =
      inputHistoryAt (memory := memory) (start + 1) := by
  have h := fold_destination_wordSegment start 1 hstart
  simpa [wordSegment] using h

/-- The history-window convention in Definition 11 agrees with the input
history immediately before the next symbol. -/
theorem historyWindow_previous {memory : ℕ} {start : ℕ} (hstart : 0 < start) :
    Finite.historyWindow (memory := memory) queenSymbol (start - 1) =
      inputHistoryAt (memory := memory) start := by
  simp only [Finite.historyWindow, inputHistoryAt, wordSegment,
    Nat.sub_add_cancel hstart]

/-- The actual word supplies a permitted path for every requested segment
whose symbols are already determined. This is Lemma 16(i)'s graph-path argument. -/
theorem permittedPath_wordSegment {memory : ℕ} {graph : Finite.HistoryGraph} {start length last : ℕ}
    (hstart : memory < start) (hend : start + length ≤ last + 1)
    (hword : graph.FollowsThrough queenSymbol last (memory := memory)) :
    Finite.PermittedPath (memory := memory) graph (inputHistoryAt (memory := memory) start)
      (wordSegment start length) := by
  induction length generalizing start with
  | zero => trivial
  | succ length ih =>
    have ht : start - 1 ∈ Finset.Icc memory last := by
      simp only [Finset.mem_Icc]
      omega
    have hallowed := (hword (start - 1) ht).2 (by omega)
    rw [historyWindow_previous (by omega), Nat.sub_add_cancel (by omega : 1 ≤ start)] at hallowed
    have hcons : wordSegment start (length + 1) =
        queenSymbol start :: wordSegment (start + 1) length := by
      have h := wordSegment_add start 1 length
      simpa [wordSegment, Nat.add_comm 1 length] using h
    rw [hcons]
    cases hanswers : graph.answers (inputHistoryAt (memory := memory) start) with
    | none => simp [hanswers] at hallowed
    | some answers =>
      refine ⟨answers, hanswers, ?_, ?_⟩
      · simpa [hanswers] using hallowed
      · rw [destination_inputHistoryAt (memory := memory) start (by omega)]
        exact ih (by omega) (by omega)

/-- If `Extend` succeeds, its output includes the actual extended queue.
Every permitted answer is retained by the generic branching calculation, so
the true board branch cannot disappear (Lemma 16(i)). -/
theorem extendBy_contains_actual {memory : ℕ} {graph : Finite.HistoryGraph}
    {start length extra last : ℕ} {out : List (List ℕ)}
    (hstart : memory < start) (hend : start + (length + extra) ≤ last + 1)
    (hword : graph.FollowsThrough queenSymbol last (memory := memory))
    (hok : Finite.extendBy (memory := memory) graph (inputHistoryAt (memory := memory) start) extra
      (wordSegment start length) = .ok out) :
    wordSegment start (length + extra) ∈ out := by
  have hpath := permittedPath_wordSegment (graph := graph)
    (start := start + length) (length := extra) (by omega) (by omega) hword
  rw [← fold_destination_wordSegment start length
    (by omega)] at hpath
  have hmem := Finite.extendBy_contains_path hpath (by simpa using hok)
  rwa [← wordSegment_add] at hmem

/-- The exact actual-queue length after a successful `Extend(k)` is the maximum
of the previous length and the requested nonnegative length. Requests already
satisfied by the queue leave the actual branch unchanged (Algorithm 1). -/
theorem extendQueue_contains_actual {memory : ℕ} {graph : Finite.HistoryGraph}
    {start length last : ℕ} {request : ℤ} {out : List (List ℕ)}
    (hstart : memory < start) (hend : start + max length request.toNat ≤ last + 1)
    (hword : graph.FollowsThrough queenSymbol last (memory := memory))
    (hok : Finite.extendQueue (memory := memory) graph (inputHistoryAt (memory := memory) start)
      (wordSegment start length) request = .ok out) :
    wordSegment start (max length request.toNat) ∈ out := by
  have hlength : length + (request.toNat - length) = max length request.toNat := by omega
  unfold Finite.extendQueue at hok
  rw [wordSegment_length] at hok
  have hmem := extendBy_contains_actual hstart (by omega) hword hok
  rwa [hlength] at hmem

/-- The last digit of a represented output history is the actual previous
queen symbol. This links local-state graph labels to the sequence in
Corollary 19's path-contraction argument. -/
theorem StateRepresented.output_last {memory n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (hmemory : 0 < memory)
    (hn : memory ≤ n) : s.output % 4 = queenSymbol (n - 1) := by
  rw [← hrep.output_eq]
  have hsplit := wordSegment_add (n - memory) (memory - 1) 1
  rw [Nat.sub_add_cancel hmemory] at hsplit
  have hindex : n - memory + (memory - 1) = n - 1 := by omega
  rw [hindex] at hsplit
  have hone : wordSegment (n - 1) 1 = [queenSymbol (n - 1)] := by simp [wordSegment]
  rw [hsplit, hone, Finite.encode_append]
  have hsymbol := queenSymbol_lt_four (n - 1)
  simp [Finite.encode, Nat.mod_eq_of_lt hsymbol]

end Queens
