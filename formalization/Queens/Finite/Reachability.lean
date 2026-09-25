import Queens.Finite.ReachabilityChunks
import Queens.Finite.StateCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact reachability of the checked invariant

Proposition 17's predecessor witnesses have been checked separately in bounded
kernel reductions. Strong induction on their distances proves that every state
is reached, and structural counting identifies the exact number of edges.
-/

namespace Queens.Finite

/-- Proposition 17: every proposed predecessor witness checks successfully.
The Lean kernel checks the recomputed transition and decreasing distance. -/
theorem predecessors_checked : ∀ i : Fin Data.states.size, ParentCheck i := by
  intro i
  have h := Array.all_eq_true.mp predecessor_states_checked i.val i.isLt
  have hm := indexedLookup_mem (lookupStateIndex_eq_getElem i.val i.isLt)
  have hlookup := stateIndex_lookup_checked (i.val, Data.states[i.val]) hm
  apply checkParentEntry_sound
  simpa only [checkParentState, hlookup] using h

private theorem reachable_of_decreasing_predecessors {α ι : Type}
    (edge : α → α → Prop) (start : α) (node : ι → α) (distance : ι → ℕ)
    (parents : ∀ i, node i = start ∨
      ∃ parent, distance parent < distance i ∧ edge (node parent) (node i)) (i : ι) :
    Relation.ReflTransGen edge start (node i) := by
  have h : ∀ d, ∀ j : ι, distance j = d →
      Relation.ReflTransGen edge start (node j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro j hj
        rcases parents j with hstart | ⟨parent, hlt, hedge⟩
        · rw [hstart]
        · exact (ih (distance parent) (by omega) parent rfl).tail hedge
  exact h (distance i) i rfl

/-- Proposition 17: every entry in the checked table is actually reached from
the initial state. Strictly decreasing witness distances justify the induction. -/
theorem table_state_reachable (i : Fin Data.states.size) :
    Relation.ReflTransGen Step initialState Data.states[i] := by
  apply reachable_of_decreasing_predecessors Step initialState
    (fun j : Fin Data.states.size => Data.states[j]) witnessDistance _ i
  intro j
  cases hp : witnessParent j with
  | none =>
      left
      simpa only [ParentCheck, hp, or_false] using predecessors_checked j
  | some parent =>
      have hc : Data.states[j] = initialState ∨
          witnessDistance parent < witnessDistance j ∧
          hasStep Data.states[parent] Data.states[j] = true := by
        simpa only [ParentCheck, hp] using predecessors_checked j
      rcases hc with hstart | hstep
      · exact Or.inl hstart
      · exact Or.inr ⟨parent, hstep.1, hasStep_iff.mp hstep.2⟩

/-- Proposition 17: table membership and reachability describe exactly the
same state set, rather than merely an over-approximation of the reached states. -/
theorem certified_iff_reachable {s : State} :
    Certified s ↔ Relation.ReflTransGen Step initialState s := by
  constructor
  · rintro ⟨i, rfl⟩
    exact table_state_reachable i
  · exact reachable_certified

/-- Proposition 17: the mathematical set of reached states is represented by
the finite state table. -/
theorem reachable_iff_mem_states {s : State} :
    Relation.ReflTransGen Step initialState s ↔ s ∈ Data.states.toList.toFinset := by
  rw [← certified_iff_reachable, List.mem_toFinset]
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro hs
    have hm : s ∈ Data.states := by simpa using hs
    obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hm
    exact ⟨⟨i, hi⟩, heq⟩

/-- Proposition 17: there are exactly 7014 reached states. The preceding
membership equivalence identifies this finite set with the actual graph reachability. -/
theorem reached_state_count : Data.states.toList.toFinset.card = 7014 := by
  rw [List.toFinset_card_of_nodup states_nodup, Array.length_toList, states_size]

/-- Proposition 17: the directed edge set of the reached state graph.
Successors are sets, so multiple branches producing the same target count once. -/
def reachedEdges : Finset (State × State) :=
  Data.states.toList.toFinset.biUnion fun source =>
    match calculate Data.historyGraph source with
    | .error _ => ∅
    | .ok next => next.toFinset.image (fun target => (source, target))

/-- Definition 14 and Proposition 17: the finite edge set contains exactly
the calculated edges whose source is reachable from the initial state. -/
theorem mem_reachedEdges {source target : State} :
    (source, target) ∈ reachedEdges ↔
      Relation.ReflTransGen Step initialState source ∧ Step source target := by
  unfold reachedEdges
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hedge⟩
    cases hc : calculate Data.historyGraph s with
    | error failure => simp [hc] at hedge
    | ok next =>
        simp only [hc, Finset.mem_image, List.mem_toFinset, Prod.mk.injEq] at hedge
        obtain ⟨t, ht, rfl, rfl⟩ := hedge
        exact ⟨reachable_iff_mem_states.mpr hs, next, hc, ht⟩
  · rintro ⟨hsource, next, hn, ht⟩
    refine ⟨source, reachable_iff_mem_states.mp hsource, ?_⟩
    simp only [hn, Finset.mem_image, List.mem_toFinset, Prod.mk.injEq]
    exact ⟨target, ht, by simp⟩

/-- Proposition 17: summing distinct successor counts counts the reached edges
exactly once. Different source vertices give disjoint sets of ordered pairs. -/
theorem reachedEdges_card_eq_stateEdgeCount : reachedEdges.card = stateEdgeCount := by
  unfold reachedEdges stateEdgeCount stateSuccessorCount
  rw [Finset.card_biUnion]
  · rw [List.sum_toFinset _ states_nodup]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    cases hc : calculate Data.historyGraph s with
    | error e => simp
    | ok next =>
      simp only [Finset.card_image_iff]
      apply Set.injOn_of_injective
      intro a b hab
      exact (Prod.mk.inj hab).2
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro edge hea heb
    cases hca : calculate Data.historyGraph a with
    | error e => simp [hca] at hea
    | ok na =>
      cases hcb : calculate Data.historyGraph b with
      | error e => simp [hcb] at heb
      | ok nb =>
        simp only [hca, hcb, Finset.mem_image, List.mem_toFinset] at hea heb
        obtain ⟨x, _, rfl⟩ := hea
        obtain ⟨y, _, heq⟩ := heb
        exact hab (Prod.mk.inj heq).1.symm

/-- Proposition 17: there are exactly 8327 directed edges in the reached graph,
with reachability and edge semantics identified by `mem_reachedEdges`. -/
theorem reached_edge_count : reachedEdges.card = 8327 := by
  rw [reachedEdges_card_eq_stateEdgeCount, state_edge_count]

end Queens.Finite
