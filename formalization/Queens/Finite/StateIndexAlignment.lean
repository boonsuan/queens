import Queens.Finite.Data

/-!
# Agreement of state indices and the invariant array

The auxiliary reachability witnesses in Proposition 17 refer to array positions.
A linear comparison with the indexed list, followed by successful self-lookups,
identifies the balanced lookup result at each such position. These are kernel
checks of the generated layout, not assumptions about the exporter.
-/

namespace Queens.Finite

set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: the indexed tree assigns the original array position to
every state. This includes both its state value and its natural-number index. -/
theorem stateIndex_alignment :
    (stateIndexEntries Data.stateIndex).map (fun entry => (entry.1, id entry.2)) =
      Data.states.toList.zipIdx.map Prod.swap := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: each proposed state-index node is found by its own index.
This checks lookup completeness on the supplied layout without assuming it. -/
theorem stateIndex_self_lookup : ∀ entry ∈ stateIndexEntries Data.stateIndex,
    indexedLookup entry.1 Data.stateIndex = some entry.2 := by
  have h : indexedAll (fun entry => decide
      (indexedLookup entry.1 Data.stateIndex = some entry.2)) Data.stateIndex = true := by
    decide +kernel
  intro entry he
  exact of_decide_eq_true (indexedAll_eq_true.mp h entry he)

/-- Proposition 17: balanced lookup at a valid natural-number position returns
exactly the state stored at that position in the original invariant array. -/
theorem lookupStateIndex_eq_getElem (i : ℕ) (hi : i < Data.states.size) :
    indexedLookup i Data.stateIndex = some Data.states[i] := by
  obtain ⟨s, hs, heq⟩ := indexedLookup_of_list_alignment stateIndex_self_lookup
    stateIndex_alignment (by simpa only [Array.length_toList] using hi)
  simpa only [id_eq, Array.getElem_toList] using hs.trans (congrArg some heq)

end Queens.Finite
