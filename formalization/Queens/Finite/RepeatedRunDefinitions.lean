import Queens.Finite.RepeatedRunData
import Queens.Finite.PathContraction

/-!
# Executable run-graph certificate obligations for Corollary 19

The lookup layout, bounded path contraction, and finite closure predicates are
separate from their kernel checks and the mathematical soundness argument.
-/

namespace Queens.Finite

/-- Corollary 19: whether a numbered forty-symbol state is immediately after
an upper output. The checked balanced layout supports fast kernel lookup. -/
def fortyStateUpper (v : ℕ) : Bool :=
  ((indexedLookup v repeatedRunTree).map RunVertexData.upper).getD false

/-- Appendix A: original state successors read from the checked balanced layout. -/
def fortyRunAdjacency : Adjacency := fun v =>
  ((indexedLookup v repeatedRunTree).map RunVertexData.successors).getD []

/-- Corollary 19: candidate remaining lengths for a fixed label and numbered
state. The lists are untrusted certificate data until checked below. -/
def repeatedRunLengths (label vertex : ℕ) : List ℕ :=
  match indexedLookup vertex repeatedRunTree with
  | none => []
  | some entry => match label with
    | 1 => entry.ones
    | 2 => entry.twos
    | 3 => entry.threes
    | _ => []

/-- Corollary 19, A275887: the claimed set of possible positive maximal
repetition lengths. In particular the exceptional missing length is ten. -/
def AllowedRepeatedRunLength (length : ℕ) : Prop :=
  1 ≤ length ∧ length ≤ 11 ∧ length ≠ 10

/-- The claimed set of repeated-run lengths is decidable. -/
instance (length : ℕ) : Decidable (AllowedRepeatedRunLength length) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Appendix A: a run-graph edge is a bounded contraction from an upper state,
through at most four further upper outputs and one to three lower outputs, to
the next upper output. Its label is the number of lower outputs. -/
def FortyRunEdge (v label w : ℕ) : Prop :=
  (∃ entry, indexedLookup v repeatedRunTree = some entry) ∧ fortyStateUpper v = true ∧
    (w, label) ∈ runTargets fortyRunAdjacency fortyStateUpper 5 v

/-- Corollary 19: local closure and boundary checks for the proposed remaining
length sets. Both outgoing labels and every possible remaining length are checked. -/
def CheckRepeatedRunVertex (v : ℕ) : Prop :=
  (∀ c ∈ ([1, 2, 3] : List ℕ), repeatedRunLengths c v ≠ [] ∧
    ∀ k ∈ repeatedRunLengths c v, k ≤ 11) ∧
  ∀ pair ∈ runTargets fortyRunAdjacency fortyStateUpper 5 v,
    ∀ c ∈ ([1, 2, 3] : List ℕ),
      (pair.2 = c → ∀ k ∈ repeatedRunLengths c pair.1,
        k + 1 ∈ repeatedRunLengths c v) ∧
      (pair.2 ≠ c → 0 ∈ repeatedRunLengths c v ∧
        ∀ k ∈ repeatedRunLengths c pair.1, 0 < k → AllowedRepeatedRunLength k)

/-- The closure and boundary obligations at a finite vertex are decidable. -/
instance (v : ℕ) : Decidable (CheckRepeatedRunVertex v) :=
  inferInstanceAs (Decidable (_ ∧ _))


end Queens.Finite
