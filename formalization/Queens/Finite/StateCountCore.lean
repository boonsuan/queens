import Queens.Finite.CertificateCore
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Distinct successor counts

Proposition 17 counts each directed edge once, even when distinct branches of
Algorithm 1 have the same successor. This file defines that count and proves
the generic sum decomposition used by the bounded kernel checks.
-/

namespace Queens.Finite

/-- Proposition 17: number of distinct successors of a state. Failed
calculations contribute zero; `certified_successors` separately rules them out
on the certified invariant. -/
def stateSuccessorCount (s : State) : ℕ :=
  match calculate Data.historyGraph s with
  | .error _ => 0
  | .ok next => next.toFinset.card

/-- Proposition 17: sum distinct successor counts over the original invariant
table. The table's checked uniqueness ensures distinct source vertices. -/
def stateEdgeCount : ℕ := (Data.states.toList.map stateSuccessorCount).sum

/-- Section 6.3 certificate support: summing a function over flattened chunks
is the sum of the individual chunk sums. This permits bounded kernel checks. -/
theorem sum_flatten_eq_sum_ofFn {α : Type} (chunks : Array (List α)) (f : α → ℕ) :
    (chunks.toList.flatten.map f).sum =
      (List.ofFn (fun i : Fin chunks.size => (chunks[i.val].map f).sum)).sum := by
  rw [List.map_flatten, List.sum_flatten]
  have heq : chunks.toList = List.ofFn (fun i : Fin chunks.size => chunks[i.val]) :=
    (List.ofFn_getElem (xs := chunks.toList)).symm
  simp only [heq, List.map_ofFn, Function.comp_def]

end Queens.Finite
