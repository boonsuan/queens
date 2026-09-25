import Queens.LocalChoice
import Queens.Finite.FinishSemantics

/-!
# Correctness with a variable history length

Lemma 16 uses twelve symbols to exclude old attacking sources. Retaining
more symbols preserves those exclusions. This file therefore proves the local
step for any history length at least twelve and any well-formed history graph.
The twelve-symbol verification and Corollary 19's forty-symbol verification
are instances of the same semantic theorem.
-/

namespace Queens

/-- **Lemma 16, candidate phase**, also used in Proposition 21. Preliminary
queue extension and candidate selection retain the actual queen choice, with
a queue long enough to finish the step and containing only determined symbols.
This shared statement separates candidate selection from the final record update. -/
theorem local_choices_exact_of_memory {memory n : ℕ} {graph : Finite.HistoryGraph}
    (hmemory : 12 ≤ memory) (hstart : memory < rowReference n)
    (hcount : 12 ≤ countReference n)
    {s : Finite.State} {queues : List (List ℕ)} {choices : List Finite.Choice}
    (hrep : StateRepresented n s memory) (hc : Finite.Condition s)
    (hword : graph.FollowsThrough queenSymbol (n - 1) (memory := memory))
    (hextend : Finite.extendQueue graph s.input s.queue s.z memory = .ok queues)
    (hchoose : Finite.allBranches queues
      (fun queue => Finite.chooseFrom graph s (s.w + 1).toNat 0 queue memory) = .ok choices) :
    ∃ (choice : Option ℕ) (length : ℕ), s.z ≤ (length : ℤ) ∧ length ≤ n - rowReference n ∧
      ChoiceMatches n choice ∧ (choice, wordSegment (rowReference n) length) ∈ choices := by
  have hcausal := hrep.requests_causal_general hcount hc
  have hqueue := hrep.queue_before_column
  have hz := hc.2.2.1
  let k := max s.queue.length s.z.toNat
  have hk : k ≤ n - rowReference n := by dsimp [k]; omega
  have hinput : inputHistoryAt (rowReference n) memory = s.input := hrep.input_eq
  have hextend' : Finite.extendQueue graph
      (inputHistoryAt (rowReference n) memory) (wordSegment (rowReference n) s.queue.length)
      s.z (memory := memory) = .ok queues := by
    rw [hinput, hrep.queue_eq]
    exact hextend
  have hactualQueue : wordSegment (rowReference n) k ∈ queues :=
    extendQueue_contains_actual hstart (by dsimp [k] at hk ⊢; omega) hword hextend'
  obtain ⟨actualChoices, hactualChoices, hchoicesSubset⟩ :=
    Finite.allBranches_branch hchoose hactualQueue
  obtain ⟨choice, length, hlength, hlimit, hmatches, hchoice⟩ :=
    chooseFrom_contains_actual hrep (by omega) hc
      (hrep.extendsActualWord_general hstart hword) (by omega) (by omega) hk hactualChoices
      (hmemory := hmemory)
  exact ⟨choice, length, by dsimp [k] at hlength; omega,
    hlimit, hmatches, hchoicesSubset _ hchoice⟩

/-- **Lemma 16 with longer histories**, as used in Corollary 19 and Appendix A.
Every successful complete calculation retains the actual next board and
extends the actual word's graph path. The lower bound on the upper-count
reference remains twelve, independently of the retained history length. -/
theorem local_step_exact_of_memory {memory n : ℕ} {graph : Finite.HistoryGraph}
    (hmemory : 12 ≤ memory) (hstart : memory < rowReference n)
    (hcount : 12 ≤ countReference n)
    (hgraph : graph.WellFormed (memory := memory))
    {s : Finite.State} {next : List Finite.State}
    (hrep : StateRepresented n s memory) (hc : Finite.Condition s)
    (hword : graph.FollowsThrough queenSymbol (n - 1) (memory := memory))
    (hcalculate : Finite.calculate graph s (memory := memory) = .ok next) :
    ∃ t ∈ next, StateRepresented (n + 1) t memory ∧
      graph.FollowsThrough queenSymbol n (memory := memory) := by
  obtain ⟨queues, choices, hextend, hchoose, hfinish⟩ :=
    Finite.calculate_decompose hcalculate
  obtain ⟨choice, length, hzlength, hlimit, hmatches, hchoice⟩ :=
    local_choices_exact_of_memory hmemory hstart hcount hrep hc hword hextend hchoose
  obtain ⟨actualNext, hactualNext, hnextSubset⟩ :=
    Finite.allBranches_branch hfinish hchoice
  obtain ⟨t, ht, hrep', hword'⟩ :=
    Finite.finishChoice_contains_actual_of_extensions_general hmemory hstart hcount
      hrep hc hword hgraph (hrep.extendsActualWord_general hstart hword)
      hmatches.eq_actual hlimit hzlength hactualNext
  exact ⟨t, hnextSubset _ ht, hrep', hword'⟩

end Queens
