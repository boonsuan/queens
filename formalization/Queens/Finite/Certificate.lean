import Queens.Finite.CertificateChunks

/-!
# The checked local invariant

Proposition 17 follows from the separately kernel-checked bounded chunks.
This file extracts semantic invariance and the reported finite graph counts.
-/

namespace Queens.Finite

set_option Elab.async false
set_option maxRecDepth 100000

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Section 6.1: the displayed starting state is included in the checked table. -/
theorem initialState_certified : Certified initialState :=
  certified_of_lookupState (by decide +kernel)

/-- Proposition 17: each certified state satisfies Condition 15. -/
theorem certified_condition {s : State} (hs : Certified s) : Condition s := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := hs
  have h := Array.all_eq_true.mp certificate_checked i hi
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- Proposition 17: every branch succeeds and returns another certified state.
The existential records successful termination of the total calculation, so this
statement cannot be satisfied by discarding an unsuccessful branch. -/
theorem certified_successors {s : State} (hs : Certified s) :
    ∃ next, calculate Data.historyGraph s = .ok next ∧
      ∀ t ∈ next, Certified t := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := hs
  have h := (Bool.and_eq_true_iff.mp (Array.all_eq_true.mp certificate_checked i hi)).2
  cases hc : calculate Data.historyGraph Data.states[i] with
  | error failure => simp [hc] at h
  | ok next =>
      refine ⟨next, rfl, ?_⟩
      have hn : next.all (fun t => (lookupState t Data.stateIndex).isSome) = true := by
        simpa [hc] using h
      intro t ht
      exact certified_of_lookupState (List.all_eq_true.mp hn t ht)

/-- Definition 14: one edge of the calculated local-state graph. -/
def Step (s t : State) : Prop :=
  ∃ next, calculate Data.historyGraph s = .ok next ∧ t ∈ next

/-- Definition 14: every edge leaving a certified state stays in the certificate. -/
theorem certified_step {s t : State} (hs : Certified s) (hst : Step s t) :
    Certified t := by
  obtain ⟨next, hn, ht⟩ := hst
  obtain ⟨next', hn', hall⟩ := certified_successors hs
  have heq : next = next' := by simpa [hn] using hn'
  subst next'
  exact hall t ht

/-- Section 6.4, the finite-state part of the induction: any finite walk of the
local calculation from the starting record stays in the certificate. -/
theorem reachable_certified {s : State}
    (h : Relation.ReflTransGen Step initialState s) : Certified s := by
  induction h with
  | refl => exact initialState_certified
  | tail _ hstep ih => exact certified_step ih hstep

/-- Section 6.4: every locally reachable record satisfies Condition 15.
The additional assertion that the actual greedy board traces such a walk is
exactly the separate semantic bridge in Lemma 16. -/
theorem reachable_condition {s : State}
    (h : Relation.ReflTransGen Step initialState s) : Condition s :=
  certified_condition (reachable_certified h)

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: the checked invariant table contains 7014 entries.
Together with `states_nodup`, this counts distinct states. -/
theorem states_size : Data.states.size = 7014 := by decide +kernel

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: every state entry recovers its own index by lookup. This
kernel check supplies both uniqueness and auxiliary witness identification. -/
theorem stateIndex_lookup_checked : ∀ entry ∈ stateIndexEntries Data.stateIndex,
    lookupState entry.2 Data.stateIndex = some entry.1 := by
  have hlookup : stateIndexAll (fun entry => decide
      (lookupState entry.2 Data.stateIndex = some entry.1)) Data.stateIndex = true := by
    decide +kernel
  intro entry he
  exact of_decide_eq_true (stateIndexAll_eq_true.mp hlookup entry he)

set_option maxHeartbeats 20000000 in
-- Kernel reduction checks the complete finite certificate at this declaration.
/-- Proposition 17: the 7014 entries in the checked invariant are distinct. -/
theorem states_nodup : Data.states.toList.Nodup := by
  have hkeys : (stateIndexEntries Data.stateIndex).map Prod.fst = List.range 7014 := by
    decide +kernel
  rw [← stateIndex_entries]
  apply nodup_values_of_nodup_keys (recover := fun s => lookupState s Data.stateIndex)
  · rw [hkeys]
    exact List.nodup_range
  · exact stateIndex_lookup_checked

end Queens.Finite
