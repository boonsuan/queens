import Queens.Finite.Encoding

/-!
# Structural properties of retained upper sources

Section 4.4 and Propositions 12–13 use one record per retained upper column.
These lemmas show that the executable source list has no duplicate source
offsets, and expose the two ordinary counts defining the adjustment `J`.
-/

namespace Queens.Finite

private theorem zipIdx_pairwise_snd (word : List ℕ) :
    word.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := by
  apply List.pairwise_map.mp
  change (word.zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

/-- Section 4.4: no history source is counted twice. -/
theorem historyColumns_offsets_nodup (history : List ℕ) :
    ((historyColumns history).map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  unfold historyColumns
  apply (zipIdx_pairwise_snd history).filterMap
  rintro ⟨a, i⟩ ⟨b, j⟩ hij c hc d hd
  dsimp only at hc hd hij
  split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc
  split at hd <;> simp only [Option.some.injEq, reduceCtorEq] at hd
  subst c d
  dsimp only
  omega

/-- Section 4.4: no queue source is counted twice. -/
theorem queueColumns_offsets_nodup (queue : List ℕ) :
    ((queueColumns queue).map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  unfold queueColumns
  apply (zipIdx_pairwise_snd queue).filterMap
  rintro ⟨a, i⟩ ⟨b, j⟩ hij c hc d hd
  dsimp only at hc hd hij
  split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc
  split at hd <;> simp only [Option.some.injEq, reduceCtorEq] at hd
  subst c d
  dsimp only
  omega

/-- Section 4.4: every source retained in the input history is before `m`. -/
theorem historyColumns_offset_neg {history : List ℕ} {column : ℤ × ℤ}
    (h : column ∈ historyColumns history) : column.1 < 0 := by
  obtain ⟨⟨symbol, i⟩, hi, heq⟩ := List.mem_filterMap.mp h
  have hbound := (List.mem_zipIdx hi).2.1
  dsimp only at heq
  split at heq <;> simp only [Option.some.injEq, reduceCtorEq] at heq
  subst column
  dsimp only
  omega

/-- Section 4.4: every source retained in the queue is at or after `m`. -/
theorem queueColumns_offset_nonneg {queue : List ℕ} {column : ℤ × ℤ}
    (h : column ∈ queueColumns queue) : 0 ≤ column.1 := by
  obtain ⟨⟨symbol, i⟩, hi, heq⟩ := List.mem_filterMap.mp h
  dsimp only at heq
  split at heq <;> simp only [Option.some.injEq, reduceCtorEq] at heq
  subst column
  dsimp only
  omega

/-- Section 4.4: each retained upper-column offset occurs exactly once in
`upperColumns`; history and queue source ranges are disjoint. -/
theorem upperColumns_offsets_nodup (s : State) (queue : List ℕ)
    (memory : ℕ := historyLength) :
    ((upperColumns s queue (memory := memory)).map Prod.fst).Nodup := by
  rw [upperColumns, List.map_append, List.nodup_append]
  refine ⟨historyColumns_offsets_nodup _, queueColumns_offsets_nodup _, ?_⟩
  intro a ha b hb
  obtain ⟨ca, hca, rfl⟩ := List.mem_map.mp ha
  obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hb
  have hneg := historyColumns_offset_neg hca
  have hnonneg := queueColumns_offset_nonneg hcb
  omega

/-- Section 4.4: in particular, the complete retained source pairs have no duplicates. -/
theorem upperColumns_nodup (s : State) (queue : List ℕ)
    (memory : ℕ := historyLength) :
    (upperColumns s queue (memory := memory)).Nodup :=
  List.Nodup.of_map Prod.fst (upperColumns_offsets_nodup s queue (memory := memory))

/-- Proposition 13: the executable adjustment is precisely the count of queue
sources below the row threshold minus history sources above that threshold. -/
theorem adjustment_eq_counts (s : State) (queue : List ℕ) (x : ℤ)
    (memory : ℕ := historyLength) :
    adjustment s queue x (memory := memory) =
      (((upperColumns s queue (memory := memory)).filter
        (fun (h, gamma) => decide (0 ≤ h ∧ h + gamma ≤ x))).length : ℤ) -
      (((upperColumns s queue (memory := memory)).filter
        (fun (h, gamma) => decide (h < 0 ∧ x < h + gamma))).length : ℤ) := rfl

end Queens.Finite
