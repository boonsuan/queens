import Queens.LocalBoard
import Queens.Word
import Queens.Finite.Local

/-!
# Relating actual records to finite-state records

The finite calculation stores `R`, `D`, and `A` as bit masks, whereas the
actual board records are finite sets. `RecordsRepresented` states precisely
the agreement of these five numerical/set records. It intentionally makes
no assertion about the three word fields; those need additional semantics
in the exactness theorem (Section 5, Lemma 16).
-/

namespace Queens

/-- Agreement of the five numerical and set records of Definition 10 with
the actual board before column `n`. Word histories and the queue are separate
parts of the full local-state interpretation. -/
structure RecordsRepresented (n : ℕ) (s : Finite.State) : Prop where
  /-- The signed candidate-window width agrees. -/
  window_eq : window n = s.w
  /-- The signed upper-count displacement agrees. -/
  upperDisplacement_eq : upperDisplacement n = s.z
  /-- The row bit mask represents precisely the actual retained row offsets. -/
  rowOffsets_eq : rowOffsets n = Finite.offsets s.R
  /-- The diagonal bit mask represents precisely the actual retained diagonal offsets. -/
  diagonalOffsets_eq : diagonalOffsets n = Finite.offsets s.D
  /-- The antidiagonal bit mask represents precisely the actual retained offsets. -/
  antidiagonalOffsets_eq : antidiagonalOffsets n = Finite.offsets s.A

/-- Condition 15 on a faithfully represented finite state gives the actual
record bounds needed to extract the diagonal discrepancy. -/
theorem RecordsRepresented.diagonalRecordBounds {n : ℕ} {s : Finite.State}
    (hrep : RecordsRepresented n s) (hcondition : Finite.Condition s) :
    DiagonalRecordBounds n := by
  constructor
  · rw [hrep.window_eq]
    exact hcondition.1
  · rw [hrep.diagonalOffsets_eq]
    exact hcondition.offsets_subset.2

/-- A represented finite state satisfying Condition 15 proves the discrepancy
bound for the actual lower queen in that column (Section 6.4). -/
theorem discrepancy_of_represented_condition {n : ℕ} {s : Finite.State}
    (hrep : RecordsRepresented n s) (hcondition : Finite.Condition s)
    (hn : q n < n) :
    |(n : ℤ) - (q n : ℤ) - (nextLowerRank n : ℤ)| ≤ 4 :=
  discrepancy_of_record_bounds hn (hrep.diagonalRecordBounds hcondition)

/-- A consecutive finite segment of the actual queen word, with its starting
index retained explicitly. History and queue lengths are explicit parameters. -/
noncomputable def wordSegment (start length : ℕ) : List ℕ :=
  (List.range length).map (fun k => queenSymbol (start + k))

/-- An actual word segment has exactly the requested number of symbols. -/
@[simp] theorem wordSegment_length (start length : ℕ) :
    (wordSegment start length).length = length := by simp [wordSegment]

/-- Reading within a word segment returns the symbol at its absolute index. -/
@[simp] theorem wordSegment_getElem (start length k : ℕ) (hk : k < length) :
    (wordSegment start length)[k]'(by simpa using hk) = queenSymbol (start + k) := by
  simp [wordSegment]

/-- Adjacent actual word segments concatenate to the segment of combined length. -/
theorem wordSegment_add (start a b : ℕ) :
    wordSegment start (a + b) = wordSegment start a ++ wordSegment (start + a) b := by
  simp [wordSegment, List.range_add, List.map_map, Function.comp_def, Nat.add_assoc]

/-- Taking an initial segment preserves its absolute starting index. -/
theorem wordSegment_take (start length k : ℕ) (hk : k ≤ length) :
    (wordSegment start length).take k = wordSegment start k := by
  unfold wordSegment
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

/-- Consuming symbols advances a segment's starting index by the number consumed. -/
theorem wordSegment_drop (start length k : ℕ) (hk : k ≤ length) :
    (wordSegment start length).drop k = wordSegment (start + k) (length - k) := by
  have hsplit := wordSegment_add start k (length - k)
  rw [Nat.add_sub_of_le hk] at hsplit
  rw [hsplit, List.drop_append_of_le_length (by simp)]
  simp

/-- Decoding the column bit of an actual symbol recovers the upper-column indicator. -/
theorem upperBit_queenSymbol (n : ℕ) : Finite.upperBit (queenSymbol n) = columnBit n := by
  have hu := columnBit_le_one n
  have hb := upperRowBit_le_one n
  unfold Finite.upperBit queenSymbol
  omega

/-- Decoding the row bit of an actual symbol recovers the upper-row indicator. -/
theorem rowBit_queenSymbol (n : ℕ) : Finite.rowBit (queenSymbol n) = upperRowBit n := by
  have hu := columnBit_le_one n
  have hb := upperRowBit_le_one n
  unfold Finite.rowBit queenSymbol
  omega

/-- Full interpretation of a local state before column `n`: five actual
records, two actual histories of the specified length, and a nonempty actual queue.
The queue ends before the next column, as required in Lemma 16. -/
structure StateRepresented (n : ℕ) (s : Finite.State)
    (memory : ℕ := Finite.historyLength) : Prop extends RecordsRepresented n s where
  /-- The input history starts at a nonnegative absolute index. -/
  history_start : memory ≤ rowReference n
  /-- The input history contains precisely the stored symbols preceding `m`. -/
  input_eq : Finite.encode (wordSegment (rowReference n - memory)
    memory) = s.input
  /-- The queue contains consecutive actual symbols starting at `m`. -/
  queue_eq : wordSegment (rowReference n) s.queue.length = s.queue
  /-- The output history contains precisely the stored symbols preceding `n`. -/
  output_eq : Finite.encode (wordSegment (n - memory)
    memory) = s.output
  /-- A local queue is nonempty (Definition 10). -/
  queue_nonempty : 0 < s.queue.length
  /-- Every queued symbol is determined by the already placed queens. -/
  queue_before_column : rowReference n + s.queue.length ≤ n

/-- Every queued symbol in a represented state is the actual symbol at the
corresponding absolute index. -/
theorem StateRepresented.queue_getElem {n memory : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) {k : ℕ} (hk : k < s.queue.length) :
    s.queue[k] = queenSymbol (rowReference n + k) := by
  have h := congrArg (fun l : List ℕ => l[k]?) hrep.queue_eq
  have hseg : k < (wordSegment (rowReference n) s.queue.length).length := by simpa using hk
  rw [List.getElem?_eq_getElem hseg, List.getElem?_eq_getElem hk, wordSegment_getElem _ _ _ hk] at h
  exact (Option.some.inj h).symm

end Queens
