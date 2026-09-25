import Queens.Finite.HistoryCore

/-!
# Kernel-efficient checking of finite history paths

The seed words in Section 6.1 and Corollary 19 are checked using successful tree
lookups rather than repeated linear membership tests. Lookup soundness converts
this executable check into the original graph-path predicate.
-/

namespace Queens.Finite

/-- Definition 11: check each complete positive-index window and each following
edge in a finite word prefix. Finding its mask supplies a vertex witness. -/
def HistoryGraph.checkFollowsThrough (graph : HistoryGraph) (symbols : ℕ → ℕ)
    (last : ℕ) (memory : ℕ := historyLength) : Bool :=
  decide (∀ t ∈ Finset.Icc memory last,
    (graph.lookup (historyWindow symbols t memory)).isSome = true ∧
      (t < last → ((graph.answers (historyWindow symbols t memory)).getD []).contains
        (symbols (t + 1)) = true))

/-- The efficient seed-word check establishes precisely the original finite
path predicate, including every listed window and permitted following label. -/
theorem HistoryGraph.checkFollowsThrough_sound {graph : HistoryGraph} {symbols : ℕ → ℕ}
    {last memory : ℕ} (h : graph.checkFollowsThrough symbols last memory = true) :
    graph.FollowsThrough symbols last memory := by
  have hc := of_decide_eq_true h
  intro t ht
  exact ⟨HistoryGraph.mem_of_lookup_isSome (hc t ht).1, (hc t ht).2⟩

end Queens.Finite
