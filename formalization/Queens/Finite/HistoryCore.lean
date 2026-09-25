import Queens.Finite.HistoryChecking

/-!
# History windows and paths for arbitrary finite graphs

Definition 11 describes consecutive fixed-length windows in the queen word.
These interfaces work at every history length: the main theorem uses twelve
symbols and Corollary 19 uses forty. They are independent of either generated
state table. `Queens.Finite.History` checks the concrete twelve-symbol graph.
-/

namespace Queens.Finite

/-- Definition 11: count labeled edges, not merely pairs of vertices. -/
def HistoryGraph.edgeCount (graph : HistoryGraph) : ℕ :=
  (graph.map (fun entry => ((List.range 4).filter (hasOffset entry.2)).length)).sum

/-- Definition 11: the window of a prescribed length ending at an absolute index.
The default length is twelve, and Corollary 19 also uses forty. -/
def historyWindow (symbols : ℕ → ℕ) (last : ℕ) (memory : ℕ := historyLength) : ℕ :=
  encode ((List.range memory).map
    (fun k => symbols (last + 1 - memory + k)))

/-- Definition 11 and Section 6.1: all complete positive-index windows through
`last` are vertices, and consecutive windows follow allowed labeled edges. -/
def HistoryGraph.FollowsThrough (graph : HistoryGraph) (symbols : ℕ → ℕ)
    (last : ℕ) (memory : ℕ := historyLength) : Prop :=
  ∀ t ∈ Finset.Icc memory last,
    historyWindow symbols t memory ∈ graph.map Prod.fst ∧
      (t < last → ((graph.answers (historyWindow symbols t memory)).getD []).contains
        (symbols (t + 1)) = true)

/-- Section 6.1: following the graph through a fixed endpoint is decidable. -/
instance (graph : HistoryGraph) (symbols : ℕ → ℕ) (last memory : ℕ) :
    Decidable (graph.FollowsThrough symbols last memory) :=
  inferInstanceAs (Decidable (∀ t ∈ Finset.Icc memory last, _))

end Queens.Finite
