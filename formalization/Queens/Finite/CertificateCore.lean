import Queens.Finite.StateIndexAlignment
import Queens.Finite.KernelChecks

/-!
# The local invariant checker and its membership interpretation

This file checks the finite part of Proposition 17 from *Greedy Queens and the
Golden Ratio*, Section 6.3. The data table is untrusted input: Lean recomputes the
successors and verifies the required properties by Lean kernel reduction.
No property of the actual infinite greedy board
is asserted here; applying this invariant there requires the identification of
Lemma 16 and the initial-board checks of Section 6.1.
-/

namespace Queens.Finite

/-- Proposition 17: a state is certified when it occurs in the generated table. -/
def Certified (s : State) : Prop := ∃ i : Fin Data.states.size, Data.states[i] = s

set_option maxRecDepth 100000 in
/-- Proposition 17: the generated search layout contains exactly the invariant
states in their original order, by projecting the checked indexed alignment. -/
theorem stateIndex_entries : (stateIndexEntries Data.stateIndex).map Prod.snd =
    Data.states.toList := by
  have h := congrArg (List.map Prod.snd) stateIndex_alignment
  simpa only [List.map_map, Function.comp_def, id_eq, Prod.snd_swap, List.zipIdx_map_fst] using h

/-- Proposition 17: successful lookup in the proposed balanced state index
gives genuine membership in the invariant. Its layout is not a trusted input. -/
theorem certified_of_lookupState {s : State}
    (h : (lookupState s Data.stateIndex).isSome = true) : Certified s := by
  cases hi : lookupState s Data.stateIndex with
  | none => simp [hi] at h
  | some i =>
    have hm : s ∈ Data.states.toList := by
      rw [← stateIndex_entries]
      exact List.mem_map.mpr ⟨(i, s), lookupState_mem hi, rfl⟩
    have hm' : s ∈ Data.states := by simpa using hm
    obtain ⟨j, hj, heq⟩ := Array.mem_iff_getElem.mp hm'
    exact ⟨⟨j, hj⟩, heq⟩

/-- Proposition 17: check Condition 15 and recompute every branch, checking that
each successor belongs to the same finite invariant. -/
def checkState (s : State) : Bool :=
  decide (Condition s) &&
    match calculate Data.historyGraph s with
    | .error _ => false
    | .ok next => next.all (fun t => (lookupState t Data.stateIndex).isSome)

end Queens.Finite
