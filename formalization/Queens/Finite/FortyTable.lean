import Queens.Finite.FortyData
import Queens.Finite.IndexedTable

/-!
# Indexed interpretation of the forty-symbol table

Corollary 19 uses one canonical tree of indexed state and adjacency records.
The public arrays are its in-order projections. A linear, key-only kernel check
identifies the stored indices with their array positions. State computations
can then use logarithmic tree lookups without trusting the tree layout.
-/

namespace Queens.Finite.Forty

set_option maxRecDepth 100000
set_option Elab.async false

/-- Corollary 19: indices of the proposed forty-symbol state table. -/
abbrev Vertex := Fin FortyData.states.size

/-- Corollary 19: the state at an indexed graph vertex. -/
def state (v : Vertex) : State := FortyData.states[v]

/-- Corollary 19: the proposed successor indices of a graph vertex. -/
def successorIndices (v : Vertex) : List ℕ := FortyData.successors[v.val]?.getD []

/-- Corollary 19: the successor states selected by the proposed adjacency. -/
def successorStates (v : Vertex) : List State :=
  (successorIndices v).filterMap (fun j => FortyData.states[j]?)

set_option maxHeartbeats 0 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Corollary 19: the stored keys enumerate precisely the positions of the
canonical table. Only natural-number keys are evaluated by this kernel check. -/
theorem vertexKeys_checked :
    (indexedEntries FortyData.vertexTable).map Prod.fst =
      List.range (indexedEntries FortyData.vertexTable).length := by
  decide +kernel

/-- A canonical entry identifies its state in the public array. -/
theorem entry_state_get? {i : ℕ} {payload : State × List ℕ}
    (hmem : (i, payload) ∈ indexedEntries FortyData.vertexTable) :
    FortyData.states[i]? = some payload.1 := by
  simpa only [FortyData.states, List.getElem?_toArray] using
    indexed_field_getElem? vertexKeys_checked Prod.fst hmem

/-- A canonical entry identifies its adjacency in the public array. -/
theorem entry_successors_get? {i : ℕ} {payload : State × List ℕ}
    (hmem : (i, payload) ∈ indexedEntries FortyData.vertexTable) :
    FortyData.successors[i]? = some payload.2 := by
  simpa only [FortyData.successors, List.getElem?_toArray] using
    indexed_field_getElem? vertexKeys_checked Prod.snd hmem

/-- A listed key is a valid index of the public state array. -/
theorem entry_index_lt {i : ℕ} {payload : State × List ℕ}
    (hmem : (i, payload) ∈ indexedEntries FortyData.vertexTable) :
    i < FortyData.states.size := by
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp (entry_state_get? hmem)
  exact hi

/-- Every public vertex has a corresponding canonical payload, with both
its state and its adjacency identified. No lookup completeness is assumed. -/
theorem entry_at_vertex (v : Vertex) :
    ∃ payload : State × List ℕ, (v.val, payload) ∈ indexedEntries FortyData.vertexTable ∧
      payload.1 = state v ∧ payload.2 = successorIndices v := by
  have hv : v.val < (indexedEntries FortyData.vertexTable).length := by
    simpa only [FortyData.states, List.size_toArray, List.length_map] using v.isLt
  let payload := (indexedEntries FortyData.vertexTable)[v.val].2
  have heq : (indexedEntries FortyData.vertexTable)[v.val] = (v.val, payload) :=
    Prod.ext (indexed_key_eq_position vertexKeys_checked hv) rfl
  have hmem : (v.val, payload) ∈ indexedEntries FortyData.vertexTable :=
    List.mem_iff_getElem.mpr ⟨v.val, hv, heq⟩
  refine ⟨payload, hmem, ?_, ?_⟩
  · have hs := entry_state_get? hmem
    rw [Array.getElem?_eq_getElem v.isLt] at hs
    exact (Option.some.inj hs).symm
  · simp only [successorIndices, entry_successors_get? hmem, Option.getD_some]

/-- Corollary 19: read target states through the balanced table. Missing
indices are discarded here but explicitly rejected by `checkVertexEntry`. -/
def fastSuccessorStates (indices : List ℕ) : List State :=
  indices.filterMap (fun j => (indexedLookup j FortyData.vertexTable).map Prod.fst)

/-- Corollary 19: check a state and its outgoing index list directly from the
canonical tree. Every index must resolve, and the resulting successor set must
agree exactly with all branches of the local calculation. -/
def checkVertexEntry (entry : ℕ × (State × List ℕ)) : Bool :=
  decide (Condition entry.2.1) &&
    entry.2.2.all (fun j => (indexedLookup j FortyData.vertexTable).isSome) &&
    match calculate FortyData.historyGraph entry.2.1 40 with
    | .error _ => false
    | .ok next => decide (next.toFinset = (fastSuccessorStates entry.2.2).toFinset)

/-- Corollary 19: a successful target lookup is the state at that exact public
index. The statement uses only lookup soundness and the checked key alignment. -/
theorem lookup_state_eq {i : ℕ} {payload : State × List ℕ}
    (hlookup : indexedLookup i FortyData.vertexTable = some payload) :
    ∃ hi : i < FortyData.states.size, state ⟨i, hi⟩ = payload.1 := by
  have hmem := indexedLookup_mem hlookup
  refine ⟨entry_index_lt hmem, ?_⟩
  have hs := entry_state_get? hmem
  rw [Array.getElem?_eq_getElem (entry_index_lt hmem)] at hs
  exact Option.some.inj hs

/-- The fast successor list has exactly the states returned by successful
lookups of the listed target indices. -/
theorem mem_fastSuccessorStates_iff {indices : List ℕ} {t : State} :
    t ∈ fastSuccessorStates indices ↔ ∃ i ∈ indices,
      ∃ payload : State × List ℕ,
        indexedLookup i FortyData.vertexTable = some payload ∧ payload.1 = t := by
  simp only [fastSuccessorStates, List.mem_filterMap, Option.map_eq_some_iff]

end Queens.Finite.Forty
