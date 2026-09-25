import Queens.Finite.CertificateCore
import Queens.Finite.Branching

/-!
# Executable checks for the sharper constants

Proposition 21 in Section 6.6 uses two additional properties of the same
7014-state invariant as Proposition 17. The first bounds `w - |D| - φ |R|`;
the second bounds `w - r - |D|` at every lower choice. This file recomputes
both properties in Lean. The candidate traversal is checked before finishing
the choices, so no choice is lost by projecting to successor states.

The real inequality follows from rational bounds on the golden ratio. All
certificate comparisons are consequently integer comparisons. The finite
checks reduce to ordinary proofs verified by the Lean kernel.
-/

namespace Queens.Finite

/-- Proposition 21: integer inequalities sufficient for the record bound.
The rational enclosure `3 / 2 ≤ φ ≤ 5 / 3` suffices on this invariant. -/
def SharpRecordCondition (s : State) : Prop :=
  5 * ((offsets s.R).card : ℤ) ≤
      3 * (s.w - ((offsets s.D).card : ℤ) + 4) ∧
    2 * (s.w - ((offsets s.D).card : ℤ) - 1) ≤
      3 * ((offsets s.R).card : ℤ)

/-- Proposition 21: the integer record condition is decidable. -/
instance (s : State) : Decidable (SharpRecordCondition s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Proposition 21: enumerate all candidate choices, including all preliminary
input extensions. Failure propagates exactly as in Algorithm 1. -/
def calculateChoices (graph : HistoryGraph) (s : State) :
    Except Failure (List Choice) := do
  let queues ← extendQueue graph s.input s.queue s.z
  allBranches queues fun queue => chooseFrom graph s (s.w + 1).toNat 0 queue

/-- Proposition 21: the upper bound on a lower choice's diagonal discrepancy.
An upper choice imposes no condition on the lower diagonal. -/
def SharpChoiceCondition (s : State) (choice : Choice) : Prop :=
  match choice.1 with
  | none => True
  | some r => s.w - (r : ℤ) - ((offsets s.D).card : ℤ) ≤ 2

/-- Proposition 21: the lower-choice bound is decidable by integer arithmetic. -/
instance (s : State) (choice : Choice) : Decidable (SharpChoiceCondition s choice) := by
  unfold SharpChoiceCondition
  split <;> infer_instance

/-- Proposition 21: check the record bounds and every candidate choice; a
failed candidate traversal rejects the state rather than discarding a branch. -/
def checkSharpState (s : State) : Bool :=
  decide (SharpRecordCondition s) &&
    match calculateChoices Data.historyGraph s with
    | .error _ => false
    | .ok choices => choices.all (fun choice => decide (SharpChoiceCondition s choice))

end Queens.Finite
