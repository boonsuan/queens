import Queens.LocalRepresentation
import Queens.LocalCandidates
import Queens.LocalGeometry
import Queens.RowCounts
import Queens.Finite.Encoding
import Queens.Finite.Sources

/-!
# Upper sources represented by the stored words

The upper-column bits in a retained actual word segment recover differences
of the actual upper count. This file connects the `(h, Γ(h))` source list of
Section 4.4 to the greedy board and establishes the retained-source exclusions
used in Lemma 16.
-/

namespace Queens

/-- A single-symbol segment contains exactly the symbol at its start. -/
@[simp] theorem wordSegment_one (start : ℕ) :
    wordSegment start 1 = [queenSymbol start] := by
  simp [wordSegment]

/-- Summing upper-column bits over a positive-index actual segment gives
the change in the upper count. This is the prefix/suffix interpretation of
`Γ` in equation (C), Section 4.4. -/
theorem sum_upperBits_wordSegment (start length : ℕ) (hstart : 0 < start) :
    upperCount (start - 1) + ((wordSegment start length).map Finite.upperBit).sum =
      upperCount (start + length - 1) := by
  induction length with
  | zero => simp [wordSegment]
  | succ length ih =>
    rw [wordSegment_add, wordSegment_one, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      upperBit_queenSymbol]
    have hstep := upperCount_succ (start + length - 1)
    rw [Nat.sub_add_cancel (show 1 ≤ start + length by omega)] at hstep
    change upperCount (start + length) =
      upperCount (start + length - 1) + columnBit (start + length) at hstep
    have hend : start + (length + 1) - 1 = start + length := by omega
    rw [hend]
    omega

/-- Prefix bits through a retained queue column give its relative upper
count. This is the nonnegative-offset part of equation (C). -/
theorem queue_prefix_upperCount {m length k : ℕ} (hm : 0 < m) (hk : k < length) :
    ((((wordSegment m length).take (k + 1)).map Finite.upperBit).sum : ℤ) =
      relativeUpperCount m (m + k) := by
  rw [wordSegment_take m length (k + 1) (by omega)]
  have hsum := sum_upperBits_wordSegment m (k + 1) hm
  have hend : m + (k + 1) - 1 = m + k := by omega
  rw [hend] at hsum
  unfold relativeUpperCount
  omega

/-- Suffix bits strictly after a retained history column give the negative
of its relative count. This is the negative-offset part of equation (C). -/
theorem history_suffix_upperCount {m length k : ℕ} (hm : length ≤ m) (hk : k < length) :
    -((((wordSegment (m - length) length).drop (k + 1)).map Finite.upperBit).sum : ℤ) =
      relativeUpperCount m (m - length + k) := by
  rw [wordSegment_drop (m - length) length (k + 1) (by omega)]
  have hstart : 0 < m - length + (k + 1) := by omega
  have hsum := sum_upperBits_wordSegment (m - length + (k + 1)) (length - (k + 1)) hstart
  have hleft : m - length + (k + 1) - 1 = m - length + k := by omega
  have hright : m - length + (k + 1) + (length - (k + 1)) - 1 = m - 1 := by omega
  rw [hleft, hright] at hsum
  unfold relativeUpperCount
  omega

private theorem mem_wordSegment_zipIdx {start length symbol k : ℕ} :
    (symbol, k) ∈ (wordSegment start length).zipIdx ↔
      k < length ∧ symbol = queenSymbol (start + k) := by
  rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨hk, hsymbol⟩
    have hk' : k < length := by simpa using hk
    exact ⟨hk', by simpa only [wordSegment_getElem start length k hk'] using hsymbol.symm⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨by simpa using hk, wordSegment_getElem start length k hk⟩

/-- The executable queue-source list contains exactly the actual upper
columns in the queue, with their correct relative counts. -/
theorem mem_queueColumns_wordSegment {m length : ℕ} (hm : 0 < m) (p : ℤ × ℤ) :
    p ∈ Finite.queueColumns (wordSegment m length) ↔
      ∃ k < length, m + k < q (m + k) ∧ p = ((k : ℤ), relativeUpperCount m (m + k)) := by
  simp only [Finite.queueColumns, List.mem_filterMap, Prod.exists, mem_wordSegment_zipIdx]
  constructor
  · rintro ⟨symbol, k, ⟨hk, rfl⟩, hpair⟩
    by_cases hu : m + k < q (m + k)
    · refine ⟨k, hk, hu, ?_⟩
      simpa only [upperBit_queenSymbol, columnBit, if_pos hu, ↓reduceIte,
        Option.some.injEq, queue_prefix_upperCount hm hk] using hpair.symm
    · simp [upperBit_queenSymbol, columnBit, hu] at hpair
  · rintro ⟨k, hk, hu, rfl⟩
    refine ⟨queenSymbol (m + k), k, ⟨hk, rfl⟩, ?_⟩
    simp only [upperBit_queenSymbol, columnBit, if_pos hu, ↓reduceIte, Option.some.injEq]
    rw [queue_prefix_upperCount hm hk]

/-- The executable history-source list contains exactly the actual upper
columns in the input history, with their correct negative relative counts. -/
theorem mem_historyColumns_wordSegment {m length : ℕ} (hm : length ≤ m) (p : ℤ × ℤ) :
    p ∈ Finite.historyColumns (wordSegment (m - length) length) ↔
      ∃ k < length, m - length + k < q (m - length + k) ∧
        p = ((k : ℤ) - length, relativeUpperCount m (m - length + k)) := by
  simp only [Finite.historyColumns, List.mem_filterMap, Prod.exists, mem_wordSegment_zipIdx]
  constructor
  · rintro ⟨symbol, k, ⟨hk, rfl⟩, hpair⟩
    by_cases hu : m - length + k < q (m - length + k)
    · refine ⟨k, hk, hu, ?_⟩
      simpa only [upperBit_queenSymbol, columnBit, if_pos hu, ↓reduceIte,
        Option.some.injEq, wordSegment_length, history_suffix_upperCount hm hk] using hpair.symm
    · simp [upperBit_queenSymbol, columnBit, hu] at hpair
  · rintro ⟨k, hk, hu, rfl⟩
    refine ⟨queenSymbol (m - length + k), k, ⟨hk, rfl⟩, ?_⟩
    simp only [upperBit_queenSymbol, columnBit, if_pos hu, ↓reduceIte, Option.some.injEq,
      wordSegment_length]
    rw [history_suffix_upperCount hm hk]

/-- Decoding a represented input history recovers the actual stored
segment. The base-four representation is justified by the four-symbol bound. -/
theorem StateRepresented.decode_input {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) :
    Finite.decode s.input memory =
      wordSegment (rowReference n - memory) memory := by
  rw [← hrep.input_eq]
  have hvalid : ∀ symbol ∈ wordSegment (rowReference n - memory)
      memory, symbol < 4 := by
    intro symbol hsymbol
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hsymbol
    exact queenSymbol_lt_four _
  simpa only [wordSegment_length] using Finite.decode_encode hvalid

/-- The stored source list represents exactly the actual upper queens in
the retained interval. This is the semantic link from the finite source
computation to the coordinates of Propositions 12–13. -/
theorem StateRepresented.mem_upperColumns {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (length : ℕ) (p : ℤ × ℤ) :
    p ∈ Finite.upperColumns (memory := memory) s (wordSegment (rowReference n) length) ↔
      ∃ i, rowReference n - memory ≤ i ∧
        i < rowReference n + length ∧ i < q i ∧
        p = ((i : ℤ) - rowReference n, relativeUpperCount (rowReference n) i) := by
  have hhistory := hrep.history_start
  have hm : 0 < rowReference n := by
    apply rowReference_pos
    have := hrep.queue_before_column
    have := hrep.queue_nonempty
    omega
  rw [Finite.upperColumns, hrep.decode_input, List.mem_append,
    mem_historyColumns_wordSegment hrep.history_start, mem_queueColumns_wordSegment hm]
  constructor
  · rintro (⟨k, hk, hu, rfl⟩ | ⟨k, hk, hu, rfl⟩)
    · refine ⟨rowReference n - memory + k, by omega, by omega, hu, ?_⟩
      congr 1
      have := hrep.history_start
      omega
    · refine ⟨rowReference n + k, by omega, by omega, hu, ?_⟩
      congr 1
      omega
  · rintro ⟨i, histart, hiend, hu, rfl⟩
    by_cases him : i < rowReference n
    · left
      let k := i - (rowReference n - memory)
      have hk : k < memory := by dsimp [k]; omega
      have hi : rowReference n - memory + k = i := by dsimp [k]; omega
      refine ⟨k, hk, by simpa only [hi] using hu, ?_⟩
      rw [hi]
      congr 1
      have := hrep.history_start
      dsimp [k]
      omega
    · right
      let k := i - rowReference n
      have hk : k < length := by dsimp [k]; omega
      have hi : rowReference n + k = i := by dsimp [k]; omega
      refine ⟨k, hk, by simpa only [hi] using hu, ?_⟩
      rw [hi]
      congr 1
      dsimp [k]
      omega

/-- Under Lemma 16's lower bound on `z` and the candidate queue-extension
bound, all attacking upper queens lie in the retained history and queue.
The right side is exactly Proposition 12's relative-coordinate test. -/
theorem upper_antidiagonal_retained_iff {memory : ℕ} {n r length : ℕ} (hn : 0 < n)
    (hz : -4 ≤ upperDisplacement n)
    (hqueue : rowReference n + length ≤ n)
    (hlength : (upperDisplacement n + (r : ℤ)) / 2 < length)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    (∃ i < n, i < q i ∧ i + q i = n + (rowReference n + r)) ↔
      ∃ i, rowReference n - memory ≤ i ∧ i < rowReference n + length ∧ i < q i ∧
        2 * ((i : ℤ) - rowReference n) + relativeUpperCount (rowReference n) i =
          upperDisplacement n + r := by
  have hm := rowReference_pos hn
  have hz' : -4 ≤ (n : ℤ) - rowReference n - (upperCount (rowReference n - 1) : ℤ) := hz
  have hlength' :
      ((n : ℤ) - rowReference n - (upperCount (rowReference n - 1) : ℤ) + r) / 2 < length :=
    hlength
  constructor
  · rintro ⟨i, hin, hi, hattack⟩
    have hold : rowReference n - memory ≤ i := by
      by_contra h
      have hearly := old_upper_source_irrelevant (r := r) hi (by omega) hz'
      omega
    have hfuture : i < rowReference n + length := by
      by_contra h
      have hlate := future_upper_antidiagonal_above hi hm (by omega) hlength'
      omega
    refine ⟨i, hold, hfuture, hi, ?_⟩
    exact (upper_antidiagonal_test hi (rowReference n) n r).mp hattack
  · rintro ⟨i, _, hiend, hi, hattack⟩
    refine ⟨i, by omega, hi, ?_⟩
    exact (upper_antidiagonal_test hi (rowReference n) n r).mpr hattack

/-- **Proposition 12 for the finite calculation.** When the input history
and queue are actual word segments and the request bound is met, the
executable upper-antidiagonal test detects exactly actual earlier attacks. -/
theorem StateRepresented.antidiagonalAttack_iff {memory : ℕ}
    {n r length : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (hn : 0 < n)
    (hz : -4 ≤ upperDisplacement n)
    (hqueue : rowReference n + length ≤ n)
    (hlength : (upperDisplacement n + (r : ℤ)) / 2 < length)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    Finite.antidiagonalAttack (memory := memory) s (wordSegment (rowReference n) length) r = true ↔
      ∃ i < n, i < q i ∧ i + q i = n + (rowReference n + r) := by
  rw [Finite.antidiagonalAttack, List.any_eq_true]
  constructor
  · rintro ⟨⟨h, gamma⟩, hmem, hattack⟩
    obtain ⟨i, histart, hiend, hi, hpair⟩ := (hrep.mem_upperColumns length (h, gamma)).mp hmem
    cases hpair
    apply (upper_antidiagonal_retained_iff (memory := memory) hn hz hqueue hlength).mpr
    refine ⟨i, histart, hiend, hi, ?_⟩
    simpa only [beq_iff_eq, hrep.upperDisplacement_eq] using hattack
  · intro hattack
    obtain ⟨i, histart, hiend, hi, hrelative⟩ :=
      (upper_antidiagonal_retained_iff (memory := memory) hn hz hqueue hlength).mp hattack
    refine ⟨((i : ℤ) - rowReference n, relativeUpperCount (rowReference n) i), ?_, ?_⟩
    · exact (hrep.mem_upperColumns length _).mpr ⟨i, histart, hiend, hi, rfl⟩
    · simpa only [beq_iff_eq, ← hrep.upperDisplacement_eq] using hrelative

/-- As a finite set, the retained source list is the injective image of the
actual retained upper columns under their relative-coordinate map. -/
theorem StateRepresented.upperColumns_toFinset {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (length : ℕ) :
    (Finite.upperColumns (memory := memory) s (wordSegment (rowReference n) length)).toFinset =
      ((Finset.Ico (rowReference n - memory) (rowReference n + length)).filter
        (fun i => i < q i)).image
          (fun i : ℕ => ((i : ℤ) - rowReference n, relativeUpperCount (rowReference n) i)) := by
  ext p
  rw [List.mem_toFinset, hrep.mem_upperColumns]
  constructor
  · rintro ⟨i, histart, hiend, hi, hpair⟩
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨histart, hiend⟩, hi⟩, hpair.symm⟩
  · intro h
    obtain ⟨i, hi, hpair⟩ := Finset.mem_image.mp h
    obtain ⟨hinterval, hupper⟩ := Finset.mem_filter.mp hi
    obtain ⟨histart, hiend⟩ := Finset.mem_Ico.mp hinterval
    exact ⟨i, histart, hiend, hupper, hpair.symm⟩

/-- Counting retained source pairs satisfying a test is the same as counting
the corresponding actual upper columns. This injective-image fact supplies
the two finite cardinalities in Proposition 13. -/
theorem StateRepresented.upperColumns_filter_card {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (length : ℕ) (P : ℤ × ℤ → Prop) [DecidablePred P] :
    (((Finite.upperColumns (memory := memory) s
      (wordSegment (rowReference n) length)).toFinset).filter P).card =
      ((Finset.Ico (rowReference n - memory) (rowReference n + length)).filter
        (fun i => i < q i ∧
          P ((i : ℤ) - rowReference n, relativeUpperCount (rowReference n) i))).card := by
  rw [hrep.upperColumns_toFinset, Finset.filter_image,
    Finset.card_image_of_injective _ (by
      intro i j hij
      have hfst := congrArg Prod.fst hij
      dsimp only at hfst
      omega)]
  rw [Finset.filter_filter]

/-- The nonnegative-offset part of `J(T-m-κ)` counts exactly the upper rows
at or below `T` coming from queue columns, as in Proposition 13. -/
theorem StateRepresented.upperColumns_addition_card {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (length T : ℕ) :
    (((Finite.upperColumns (memory := memory) s
      (wordSegment (rowReference n) length)).toFinset).filter
      (fun p => 0 ≤ p.1 ∧ p.1 + p.2 ≤
        (T : ℤ) - rowReference n - (countReference n : ℤ))).card =
      ((Finset.Ico (rowReference n) (rowReference n + length)).filter
        (fun i => i < q i ∧ q i ≤ T)).card := by
  rw [hrep.upperColumns_filter_card]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨histart, hiend⟩, hi, hnonneg, hrelative⟩
    have hrow := upper_row_relative hi (rowReference n)
    unfold countReference at hrelative
    exact ⟨⟨by omega, hiend⟩, hi, by omega⟩
  · rintro ⟨⟨histart, hiend⟩, hi, hiT⟩
    have hrow := upper_row_relative hi (rowReference n)
    refine ⟨⟨by omega, hiend⟩, hi, by omega, ?_⟩
    unfold countReference
    omega

/-- The negative-offset part of `J(T-m-κ)` counts exactly the upper rows
above `T` whose columns lie in the input history, as in Proposition 13. -/
theorem StateRepresented.upperColumns_removal_card {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (length T : ℕ) :
    (((Finite.upperColumns (memory := memory) s
      (wordSegment (rowReference n) length)).toFinset).filter
      (fun p => p.1 < 0 ∧
        (T : ℤ) - rowReference n - (countReference n : ℤ) < p.1 + p.2)).card =
      ((Finset.Ico (rowReference n - memory) (rowReference n)).filter
        (fun i => i < q i ∧ T < q i)).card := by
  rw [hrep.upperColumns_filter_card]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨histart, hiend⟩, hi, hnegative, hrelative⟩
    have hrow := upper_row_relative hi (rowReference n)
    unfold countReference at hrelative
    exact ⟨⟨histart, by omega⟩, hi, by omega⟩
  · rintro ⟨⟨histart, hiend⟩, hi, hiT⟩
    have hrow := upper_row_relative hi (rowReference n)
    refine ⟨⟨histart, by omega⟩, hi, by omega, ?_⟩
    unfold countReference
    omega

private theorem length_filter_eq_card_filter_toFinset {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (P : α → Prop) [DecidablePred P] :
    (l.filter (fun x => decide (P x))).length = (l.toFinset.filter P).card := by
  rw [← List.toFinset_card_of_nodup (hl.filter _), List.toFinset_filter]
  simp only [decide_eq_true_eq]

/-- **Proposition 13 for the executable source list.** Assuming the omitted
old and future sources lie on the stated sides of the row threshold, the
finite adjustment computes the actual upper-row count minus `κ`. -/
theorem StateRepresented.adjustment_eq_upperRowCount {memory : ℕ}
    {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (length T : ℕ)
    (hold : ∀ i < rowReference n - memory, i < q i → q i ≤ T)
    (hfuture : ∀ i, rowReference n + length ≤ i → i < q i → T < q i) :
    Finite.adjustment (memory := memory) s (wordSegment (rowReference n) length)
      ((T : ℤ) - rowReference n - (countReference n : ℤ)) =
      (upperRowCount T : ℤ) - (countReference n : ℤ) := by
  have hnodup :=
    Finite.upperColumns_nodup (memory := memory) s (wordSegment (rowReference n) length)
  rw [Finite.adjustment_eq_counts (memory := memory),
    length_filter_eq_card_filter_toFinset _ hnodup,
    length_filter_eq_card_filter_toFinset _ hnodup,
    hrep.upperColumns_addition_card, hrep.upperColumns_removal_card]
  have hm : 0 < rowReference n := by
    apply rowReference_pos
    have := hrep.queue_before_column
    have := hrep.queue_nonempty
    omega
  have hcount := upperRowCount_eq_adjustment (rowReference n - memory)
    (rowReference n) (rowReference n + length) T hm hold hfuture
  unfold countReference
  omega

/-- Under Lemma 16's bounds, the finite adjustment gives the actual row
count at either output threshold, `n - 1` or `n`. -/
theorem StateRepresented.adjustment_eq_upperRowCount_near_column {memory : ℕ}
    {n length T : ℕ} {s : Finite.State} (hrep : StateRepresented n s memory)
    (hz : -4 ≤ upperDisplacement n) (hlength : upperDisplacement n ≤ length)
    (hTlower : n - 1 ≤ T) (hTupper : T ≤ n)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    Finite.adjustment (memory := memory) s (wordSegment (rowReference n) length)
      ((T : ℤ) - rowReference n - (countReference n : ℤ)) =
      (upperRowCount T : ℤ) - (countReference n : ℤ) := by
  apply hrep.adjustment_eq_upperRowCount
  · intro i hi hupper
    have hold : i + 13 ≤ rowReference n := by omega
    have hrow := (old_upper_source_irrelevant (n := n) (r := 0) hupper hold hz).1
    omega
  · intro i hi hupper
    have hm : 0 < rowReference n := by
      apply rowReference_pos
      have := hrep.queue_before_column
      have := hrep.queue_nonempty
      omega
    have hrow := future_upper_row_above hupper hm hi hlength
    omega

/-- The output bit computed by Algorithm 1 agrees with the actual row bit.
This is the output-symbol part of Lemma 16, combining Proposition 13 at
the two adjacent thresholds. -/
theorem StateRepresented.adjustment_difference_eq_upperRowBit {memory : ℕ}
    {n length : ℕ} {s : Finite.State} (hrep : StateRepresented n s memory) (hn : 0 < n)
    (hz : -4 ≤ upperDisplacement n) (hlength : upperDisplacement n ≤ length)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    Finite.adjustment (memory := memory) s (wordSegment (rowReference n) length) s.z -
      Finite.adjustment (memory := memory) s (wordSegment (rowReference n) length) (s.z - 1) =
        (upperRowBit n : ℤ) := by
  have hcurrent := hrep.adjustment_eq_upperRowCount_near_column hz hlength
    (Nat.sub_le n 1) (le_refl n)
  have hprevious := hrep.adjustment_eq_upperRowCount_near_column hz hlength
    (le_refl (n - 1)) (Nat.sub_le n 1)
  have hcurrentThreshold : (n : ℤ) - rowReference n - (countReference n : ℤ) = s.z :=
    hrep.upperDisplacement_eq
  have hpreviousThreshold :
      ((n - 1 : ℕ) : ℤ) - rowReference n - (countReference n : ℤ) = s.z - 1 := by
    omega
  rw [hcurrentThreshold] at hcurrent
  rw [hpreviousThreshold] at hprevious
  have hbit := upperRowBit_eq_count_difference hn
  omega

/-- All executable candidate tests agree with actual availability when the
extended queue is an actual segment long enough for the requested candidate.
This combines the set-mask representation, queue row bit, and Proposition 12
into the exact test used in Algorithm 1's candidate loop. -/
theorem StateRepresented.candidate_tests_iff {memory : ℕ}
    {n r length : ℕ} {s : Finite.State} (hrep : StateRepresented n s memory) (hn : 0 < n)
    (hr : (r : ℤ) ≤ window n) (hrlength : r < length)
    (hz : -4 ≤ upperDisplacement n) (hqueue : rowReference n + length ≤ n)
    (hantiLength : (upperDisplacement n + (r : ℤ)) / 2 < length)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    Available n (rowReference n + r) (fun i => q i.val) ↔
      Finite.hasOffset s.R r = false ∧
      Finite.hasOffset s.D (s.w - (r : ℤ)).toNat = false ∧
      Finite.hasOffset s.A r = false ∧
      Finite.rowBit (((wordSegment (rowReference n) length)[r]?).getD 0) = 0 ∧
      Finite.antidiagonalAttack (memory := memory) s
        (wordSegment (rowReference n) length) r = false := by
  have hrow : Finite.rowBit (((wordSegment (rowReference n) length)[r]?).getD 0) =
      upperRowBit (rowReference n + r) := by
    rw [List.getElem?_eq_getElem (by simpa using hrlength)]
    simp only [Option.getD_some, wordSegment_getElem _ _ _ hrlength, rowBit_queenSymbol]
  rw [available_candidate_iff hn hr, hrow]
  unfold LowerCandidateClear
  rw [hrep.rowOffsets_eq, hrep.diagonalOffsets_eq, hrep.antidiagonalOffsets_eq,
    hrep.window_eq]
  simp only [Finite.mem_offsets, Bool.not_eq_true]
  rw [← hrep.antidiagonalAttack_iff hn hz hqueue hantiLength]
  simp only [Bool.not_eq_true]

end Queens
