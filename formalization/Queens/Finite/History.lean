import Queens.Finite.Data
import Queens.Finite.HistoryCore

/-!
# The checked history graph

This file checks the twelve-symbol presentation of Definition 11 and
Proposition 17: encodings are bounded and unique, every labeled edge has a
listed destination, and the vertex and edge counts agree with Section 6.2.
The graph interfaces for arbitrary history lengths are in `HistoryCore`;
these checks concern the concrete graph used for the main theorem.
-/

namespace Queens.Finite

set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: the supplied graph has no duplicate or malformed vertices,
and every allowed transition stays inside it. The balanced-table checker reduces
to an ordinary proof checked by the Lean kernel. -/
theorem historyGraph_wellFormed : Data.historyGraph.WellFormed :=
  checkHistoryGraph_sound (by decide +kernel)

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Section 6.2 and Proposition 17: the graph contains 2092 vertices. -/
theorem historyGraph_vertex_count : Data.historyGraph.length = 2092 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Section 6.2 and Proposition 17: the graph contains 2603 labeled edges. -/
theorem historyGraph_edge_count : Data.historyGraph.edgeCount = 2603 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: every listed vertex has an outgoing edge, so requests
at a graph vertex never terminate for lack of an answer. -/
theorem historyGraph_no_dead_ends : ∀ entry ∈ Data.historyGraph, entry.2 ≠ 0 := by
  decide +kernel

end Queens.Finite
