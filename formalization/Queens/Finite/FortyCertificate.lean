import Queens.Finite.FortyStateChecks
import Queens.Finite.HistoryCore
import Queens.Finite.FortyHistoryChecks

/-!
# The forty-symbol finite invariant

Corollary 19 (Section 6.5) repeats the finite verification with forty-symbol
histories. The proposed indexed edges are checked against **all** successors of
`calculate`, so no branch can be discarded. Indices are checked before use, and
the mathematical interface supplies genuine table witnesses independently of
how the proposed graph was generated.

The finite checks are evaluated by the Lean kernel in bounded, serialized
chunks. Balanced lookup is connected to the public arrays by ordinary proofs;
neither the generator nor the executable compiler is trusted for correctness.
-/

namespace Queens.Finite.Forty

set_option maxRecDepth 100000
set_option Elab.async false

-- Keep symbolic vertices and calculations abstract during elaboration;
-- expanding the generated table would make definitional equality needlessly costly.
attribute [local irreducible] state successorIndices calculate

/-- Corollary 19: check record bounds, every index, and exact equality of the
proposed and calculated successor sets. Failure of any branch rejects the vertex. -/
def checkVertex (v : Vertex) : Bool :=
  decide (Condition (state v)) &&
    (successorIndices v).all (fun j => decide (j < FortyData.states.size)) &&
    match calculate FortyData.historyGraph (state v) 40 with
    | .error _ => false
    | .ok next => decide (next.toFinset = (successorStates v).toFinset)

/-- Corollary 19: the finite data have exactly the reported numbers of
history vertices, history edges, state-table entries, and indexed state edges. -/
theorem data_sizes :
    FortyData.historyGraph.length = 16876 ∧
    FortyData.historyGraph.edgeCount = 17499 ∧
    FortyData.states.size = 29267 ∧
    FortyData.successors.size = FortyData.states.size ∧
    (FortyData.successors.toList.map List.length).sum = 30000 := by
  simp only [FortyData.states, FortyData.successors, List.size_toArray,
    List.length_map, List.toList_toArray]
  decide +kernel

/-- Corollary 19: the proposed forty-symbol history graph is well formed;
every allowed output edge has a listed destination. -/
theorem historyGraph_wellFormed : FortyData.historyGraph.WellFormed 40 := by
  exact checkHistoryGraph_sound historyGraph_checked

/-- The tree check applies to the canonical payload of every public vertex. -/
private theorem vertex_checked (v : Vertex) :
    checkVertexEntry (v.val, state v, successorIndices v) = true := by
  obtain ⟨payload, hmem, hstate, hedges⟩ := entry_at_vertex v
  have h := indexedAll_eq_true.mp vertexTable_checked (v.val, payload) hmem
  have hp : payload = (state v, successorIndices v) := Prod.ext hstate hedges
  rw [hp] at h
  exact h

/-- Every listed target resolves in the canonical table. -/
private theorem successor_lookup {v : Vertex} {j : ℕ}
    (hj : j ∈ successorIndices v) :
    ∃ payload, indexedLookup j FortyData.vertexTable = some payload := by
  have h := vertex_checked v
  simp only [checkVertexEntry, Bool.and_eq_true_iff] at h
  have hj' := List.all_eq_true.mp h.1.2 j hj
  cases heq : indexedLookup j FortyData.vertexTable with
  | none => simp only [heq, Option.isSome_none, Bool.false_eq_true] at hj'
  | some payload => exact ⟨payload, rfl⟩

/-- Corollary 19: the seed before column 80 is vertex zero. -/
theorem initialState_eq_state_zero :
    FortyData.initialState = state ⟨0, by rw [data_sizes.2.2.1]; omega⟩ := by
  have h : (indexedLookup 0 FortyData.vertexTable).map Prod.fst =
      some FortyData.initialState := by decide +kernel
  obtain ⟨payload, hlookup, hstate⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hbound, heq⟩ := lookup_state_eq hlookup
  exact hstate.symm.trans heq.symm

/-- Corollary 19: an indexed graph state satisfies Condition 15. -/
theorem state_condition (v : Vertex) : Condition (state v) := by
  have h := vertex_checked v
  simp only [checkVertexEntry, Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.1.1

/-- Corollary 19: every proposed successor index is in range. -/
theorem successorIndex_lt {v : Vertex} {j : ℕ} (hj : j ∈ successorIndices v) :
    j < FortyData.states.size := by
  obtain ⟨payload, hlookup⟩ := successor_lookup hj
  exact entry_index_lt (indexedLookup_mem hlookup)

/-- The balanced lookup and the public indexed graph have the same targets. -/
private theorem mem_fastSuccessorStates_vertex_iff {v : Vertex} {t : State} :
    t ∈ fastSuccessorStates (successorIndices v) ↔
      ∃ w : Vertex, w.val ∈ successorIndices v ∧ state w = t := by
  rw [mem_fastSuccessorStates_iff]
  constructor
  · rintro ⟨j, hj, payload, hlookup, hstate⟩
    obtain ⟨hjbound, heq⟩ := lookup_state_eq hlookup
    exact ⟨⟨j, hjbound⟩, hj, heq.trans hstate⟩
  · rintro ⟨w, hw, heq⟩
    obtain ⟨payload, hlookup⟩ := successor_lookup hw
    obtain ⟨hwbound, hstate⟩ := lookup_state_eq hlookup
    exact ⟨w.val, hw, payload, hlookup, hstate.symm.trans heq⟩

/-- Corollary 19: successful indexed adjacency identifies exactly the states
in the proposed successor list, including a valid index witness. -/
theorem mem_successorStates_iff {v : Vertex} {t : State} :
    t ∈ successorStates v ↔
      ∃ w : Vertex, w.val ∈ successorIndices v ∧ state w = t := by
  simp only [successorStates, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, heq⟩
    have hbound := successorIndex_lt hj
    refine ⟨⟨j, hbound⟩, hj, ?_⟩
    unfold state
    change FortyData.states[j] = t
    exact Option.some.inj ((Array.getElem?_eq_getElem hbound).symm.trans heq)
  · rintro ⟨w, hw, heq⟩
    refine ⟨w.val, hw, ?_⟩
    rw [Array.getElem?_eq_getElem w.isLt]
    unfold state at heq
    exact congrArg some heq

/-- The result component of both successor-set checkers. Keeping this small
function abstract avoids expanding the generated graph in its soundness proof. -/
private def checkResult (result : Except Failure (List State))
    (expected : List State) : Bool :=
  match result with
  | .error _ => false
  | .ok next => decide (next.toFinset = expected.toFinset)

/-- Decode the result component before specializing it to the generated graph. -/
private theorem checked_result_success {result : Except Failure (List State)}
    {expected : List State} (h : checkResult result expected = true) :
    ∃ next, result = .ok next ∧ next.toFinset = expected.toFinset := by
  cases result with
  | error failure => exact Bool.noConfusion h
  | ok next => exact ⟨next, rfl, of_decide_eq_true h⟩

/-- A successful calculation with the prescribed successor set passes the
result component of the original array-based checker. -/
private theorem checked_result_of_eq {result : Except Failure (List State)}
    {next expected : List State} (hresult : result = .ok next)
    (hset : next.toFinset = expected.toFinset) : checkResult result expected = true := by
  rw [hresult]
  exact decide_eq_true hset

/-- Corollary 19: all branches terminate, and their successor states are
exactly the indexed outgoing edges. This is the interface used to lift the
actual board to an indexed path before contracting runs and gaps. -/
theorem calculated_successors (v : Vertex) :
    ∃ next, calculate FortyData.historyGraph (state v) 40 = .ok next ∧
      ∀ t, t ∈ next ↔ ∃ w : Vertex,
        w.val ∈ successorIndices v ∧ state w = t := by
  have h := vertex_checked v
  simp only [checkVertexEntry, Bool.and_eq_true_iff] at h
  obtain ⟨next, hnext, hset⟩ := checked_result_success h.2
  refine ⟨next, hnext, ?_⟩
  intro t
  rw [← List.mem_toFinset, hset, List.mem_toFinset,
    mem_fastSuccessorStates_vertex_iff]

/-- Corollary 19: every public vertex passes the complete local calculation,
with exactly the proposed adjacency set. This follows from the bounded kernel
checks through the proved table-index correspondence. -/
theorem certificate_checked (v : Vertex) : checkVertex v = true := by
  unfold checkVertex
  apply Bool.and_eq_true_iff.mpr
  refine ⟨Bool.and_eq_true_iff.mpr ⟨by simpa using state_condition v, ?_⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro j hj
    simpa using successorIndex_lt hj
  · obtain ⟨next, hnext, hexact⟩ := calculated_successors v
    apply checked_result_of_eq hnext
    ext t
    simpa only [List.mem_toFinset, mem_successorStates_iff] using hexact t

/-- Corollary 19: table membership is the finite invariant underlying the
forty-symbol verification. -/
def Certified (s : State) : Prop := ∃ v : Vertex, state v = s

/-- Corollary 19: the actual-prefix starting record belongs to the invariant. -/
theorem initialState_certified : Certified FortyData.initialState :=
  ⟨⟨0, by rw [data_sizes.2.2.1]; omega⟩, initialState_eq_state_zero.symm⟩

/-- Corollary 19: every state in the finite invariant satisfies Condition 15. -/
theorem certified_condition {s : State} (hs : Certified s) : Condition s := by
  obtain ⟨v, rfl⟩ := hs
  exact state_condition v

/-- Corollary 19: every calculated successor of a certified state is certified,
and every branch of its calculation succeeds. -/
theorem certified_successors {s : State} (hs : Certified s) :
    ∃ next, calculate FortyData.historyGraph s 40 = .ok next ∧
      ∀ t ∈ next, Certified t := by
  obtain ⟨v, rfl⟩ := hs
  obtain ⟨next, hnext, hexact⟩ := calculated_successors v
  refine ⟨next, hnext, ?_⟩
  intro t ht
  obtain ⟨w, _, hw⟩ := (hexact t).mp ht
  exact ⟨w, hw⟩

end Queens.Finite.Forty
