import Queens.Finite.Certificate
import Queens.Finite.ReachabilityData
import Queens.Finite.StateIndexAlignment
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact reachability of the finite state graph

Proposition 17 reports the number of *reached* states. The safety proof only
needs the closed invariant in `Certificate`; this file separately checks that
every entry of that invariant can actually be reached from the initial state.

The auxiliary data provide a distance and predecessor index for each entry.
Lean recomputes each predecessor's successors, checks the edge and strict
distance decrease, and uses strong induction to establish reachability. Thus a
malformed predecessor, a cyclic witness, or a disconnected extra state cannot
make this check pass. The extra witnesses do not enter the main theorem's safety
argument.
-/

namespace Queens.Finite

set_option Elab.async false
set_option maxRecDepth 100000

/-- Proposition 17: a decidable test for a calculated state-graph edge. -/
def hasStep (s t : State) : Bool :=
  match calculate Data.historyGraph s with
  | .error _ => false
  | .ok next => next.any (fun candidate => decide (candidate = t))

/-- Definition 14: successful executable edge testing is exactly the mathematical
state-graph edge relation used by the invariant proof. -/
theorem hasStep_iff {s t : State} : hasStep s t = true ↔ Step s t := by
  unfold hasStep Step
  cases calculate Data.historyGraph s <;> simp

/-- Proposition 17: the proposed distance of a state-table entry. Defaults are
harmless because every predecessor edge and strict decrease must pass the check. -/
def witnessDistance (i : Fin Data.states.size) : ℕ :=
  (Data.predecessors[i.val]?.getD (0, 0)).1

/-- Proposition 17: a proposed predecessor, with its index checked against the
state table size before use. An out-of-range witness is rejected. -/
def witnessParent (i : Fin Data.states.size) : Option (Fin Data.states.size) :=
  let parent := (Data.predecessors[i.val]?.getD (0, 0)).2
  if h : parent < Data.states.size then some ⟨parent, h⟩ else none

/-- Proposition 17: each entry is the initial state or has a genuine incoming
edge from a table entry with a strictly smaller nonnegative distance. -/
def ParentCheck (i : Fin Data.states.size) : Prop :=
  Data.states[i] = initialState ∨
    match witnessParent i with
    | none => False
    | some parent => witnessDistance parent < witnessDistance i ∧
        hasStep Data.states[parent] Data.states[i] = true

/-- Proposition 17: checking an individual reachability witness is decidable. -/
instance (i : Fin Data.states.size) : Decidable (ParentCheck i) := by
  unfold ParentCheck
  cases witnessParent i <;> infer_instance

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: the balanced auxiliary table carries exactly the original
predecessor array, with its natural-number positions preserved. -/
theorem predecessorIndex_alignment :
    (indexedEntries Data.predecessorIndex).map (fun entry => (entry.1, id entry.2)) =
      Data.predecessors.toList.zipIdx.map Prod.swap := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: every auxiliary predecessor record can be recovered by
its own index in the proposed balanced layout. -/
theorem predecessorIndex_self_lookup : ∀ entry ∈ indexedEntries Data.predecessorIndex,
    indexedLookup entry.1 Data.predecessorIndex = some entry.2 := by
  have h : indexedAll (fun entry => decide
      (indexedLookup entry.1 Data.predecessorIndex = some entry.2))
        Data.predecessorIndex = true := by
    decide +kernel
  intro entry he
  exact of_decide_eq_true (indexedAll_eq_true.mp h entry he)

/-- Proposition 17: balanced predecessor lookup agrees with ordinary array
indexing. Only the checked agreement lemmas justify this replacement. -/
theorem lookupPredecessor_eq_getElem (i : ℕ) (hi : i < Data.predecessors.size) :
    indexedLookup i Data.predecessorIndex = some Data.predecessors[i] := by
  obtain ⟨record, hr, heq⟩ := indexedLookup_of_list_alignment predecessorIndex_self_lookup
    predecessorIndex_alignment (by simpa only [Array.length_toList] using hi)
  simpa only [id_eq, Array.getElem_toList] using hr.trans (congrArg some heq)

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: there is one proposed predecessor record for every state. -/
theorem predecessors_size : Data.predecessors.size = Data.states.size := by
  decide +kernel

/-- Proposition 17: check a reachability witness using bounded-depth lookups.
Both the actual predecessor edge and its strictly smaller distance are checked. -/
def checkParentEntry (entry : ℕ × State) : Bool :=
  if entry.2 = initialState then true else
    match indexedLookup entry.1 Data.predecessorIndex with
    | none => false
    | some (distance, parent) =>
      decide (parent < Data.states.size) &&
        match indexedLookup parent Data.predecessorIndex, indexedLookup parent Data.stateIndex with
        | some parentRecord, some parentState =>
          decide (parentRecord.1 < distance) && hasStep parentState entry.2
        | _, _ => false

/-- Proposition 17: the optimized reachability check entails the original
array-indexed witness assertion. A failed or mismatched lookup cannot supply it. -/
theorem checkParentEntry_sound (i : Fin Data.states.size)
    (h : checkParentEntry (i.val, Data.states[i.val]) = true) : ParentCheck i := by
  by_cases hstart : Data.states[i.val] = initialState
  · exact Or.inl hstart
  · unfold checkParentEntry at h
    simp only [hstart, if_false] at h
    have hic : i.val < Data.predecessors.size := by rw [predecessors_size]; exact i.isLt
    rw [lookupPredecessor_eq_getElem i.val hic] at h
    have hp : Data.predecessors[i.val].2 < Data.states.size :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hpc : Data.predecessors[i.val].2 < Data.predecessors.size := by
      rw [predecessors_size]
      exact hp
    have hc := (Bool.and_eq_true_iff.mp h).2
    change (match indexedLookup Data.predecessors[i.val].2 Data.predecessorIndex,
        indexedLookup Data.predecessors[i.val].2 Data.stateIndex with
      | some parentRecord, some parentState =>
        decide (parentRecord.1 < Data.predecessors[i.val].1) &&
          hasStep parentState Data.states[i.val]
      | _, _ => false) = true at hc
    rw [lookupPredecessor_eq_getElem _ hpc, lookupStateIndex_eq_getElem _ hp] at hc
    obtain ⟨hd, hedge⟩ := Bool.and_eq_true_iff.mp hc
    right
    simp only [witnessParent, Array.getElem?_eq_getElem hic, Option.getD_some, dif_pos hp]
    constructor
    · simpa only [witnessDistance, Array.getElem?_eq_getElem hic,
        Array.getElem?_eq_getElem hpc, Option.getD_some] using of_decide_eq_true hd
    · exact hedge

/-- Proposition 17: check the predecessor witness of a state after recovering
its checked index. Failed state lookup rejects the witness. -/
def checkParentState (s : State) : Bool :=
  match lookupState s Data.stateIndex with
  | none => false
  | some i => checkParentEntry (i, s)

end Queens.Finite
