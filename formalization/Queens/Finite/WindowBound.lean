import Queens.SqrtFive
import Queens.Finite.Local

/-!
# Window bounds and the error term of a state

Section 6.6 attaches bounds `lo(W) ≤ hi(W)` on the counting error to each
vertex `W` of the history graph, and compares them with the term
`Y(S) = w - |D| + 1 - z / φ` of a state `S`. This file defines the record that
stores a proposed pair of window bounds, and `Y(S)` itself.

## Implementation notes

The window bounds lie in `ℚ(√5)` with denominators dividing 8. A
`WindowBound` therefore stores `8 lo(W)` and `8 hi(W)` as elements of `ℤ√5`,
whose order is decidable by integer arithmetic. It also stores the index of a
state whose output history is `W`, which witnesses that `W` is an output history.
-/

namespace Queens.Finite

open scoped goldenRatio

/-- Proposition 24: the proposed window bounds of one history-graph vertex,
scaled by 8 into `ℤ√5`, with the index of a state having this output history. -/
structure WindowBound where
  /-- Eight times the lower window bound `lo(W)`. -/
  lo : ZSqrtFive
  /-- Eight times the upper window bound `hi(W)`. -/
  hi : ZSqrtFive
  /-- Index in the state table of a state whose output history is `W`. -/
  witness : ℕ

/-- Section 6.6: the term `Y(S) = w - |D| + 1 - z / φ` of a state `S`, which
appears in the one-step error identity (Lemma 21). -/
noncomputable def errorTerm (s : State) : ℝ :=
  (s.w : ℝ) - ((offsets s.D).card : ℝ) + 1 - (s.z : ℝ) / φ

end Queens.Finite
