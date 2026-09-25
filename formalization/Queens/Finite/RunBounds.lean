import Queens.Finite.Data

/-!
# Finite exclusions for the basic runs and gaps

For the first, second, fourth, and fifth rows of Corollary 19, only the column
bits of the twelve-symbol history graph are needed. Every vertex has an upper
column among its first four symbols and a lower column among its first six.
The transfer to the actual infinite word is proved in `Queens.RunsAndGaps`.
-/

namespace Queens.Finite


/-- Corollary 19: the initial `length` column bits of a decoded history are
not all equal to `bit`. Option-valued indexing makes this a total finite test. -/
def HistoryHasDifferentBit (history length bit : ℕ) : Prop :=
  ∃ i : Fin length, upperBit ((decode history historyLength)[i.val]?.getD 0) ≠ bit

/-- The finite forbidden-block test is decidable. -/
instance (history length bit : ℕ) : Decidable (HistoryHasDifferentBit history length bit) :=
  inferInstanceAs (Decidable (∃ _i : Fin length, _))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19, exclusion bounds: no history vertex starts with four lower
columns or six upper columns. This finite fact is checked using `decide +kernel`. -/
theorem historyGraph_run_bounds : ∀ v ∈ Data.historyGraph.map Prod.fst,
    HistoryHasDifferentBit v 4 0 ∧ HistoryHasDifferentBit v 6 1 := by
  decide +kernel

end Queens.Finite
