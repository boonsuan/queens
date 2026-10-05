import Queens.Finite.Branching
import Queens.Finite.CertificateCore
import Queens.Finite.WindowData

/-!
# Executable checks of the window bounds

Proposition 24 in Section 6.6 checks inequalities between the proposed window
bounds, the term `Y(S)` of each state, and the lower choices of each branch of
the calculation. This file states those inequalities after clearing
denominators, as comparisons in `ℤ√5`, and combines them into Boolean checks
for one state and for one vertex. The generated modules `WindowChunks` and
`WindowVertexChecks` verify the checks on all states and vertices by kernel
reduction; `WindowCertificate` translates them into real inequalities.

Every failure, including a missing window bound or a failed calculation,
rejects the check. No branch or lower choice is discarded.

## Implementation notes

Multiplying by 16 turns each inequality into one between elements of `ℤ√5`:
`16 Y(S) = 16 (w - |D| + 1) + 8 z - 8 z √5`, and `16 x / φ = 8 x (√5 - 1)`.
The window bounds are stored as `8 lo(W)` and `8 hi(W)`.
-/

namespace Queens.Finite

/-- Section 6.6: the proposed window bounds of an encoded vertex, if any. -/
def windowBound? (vertex : ℕ) : Option WindowBound :=
  indexedLookup vertex Data.windowBounds

/-- `2 / φ = √5 - 1` as an element of `ℤ√5`. -/
def twiceInvGoldenRatio : ZSqrtFive := ⟨-1, 1⟩

/-- `16 Y(S)` as an element of `ℤ√5`, where `Y(S) = w - |D| + 1 - z / φ`. -/
def scaledErrorTerm (s : State) : ZSqrtFive :=
  ⟨16 * (s.w - ((offsets s.D).card : ℤ) + 1) + 8 * s.z, -8 * s.z⟩

/-- Definition 22 at one state, multiplied by 16: with `V = H_in(S)` and
`W = H_out(S)`, `lo(W) ≤ Y(S) - hi(V) / φ` and `Y(S) - lo(V) / φ ≤ hi(W)`. -/
def ConsistentAt (s : State) (input output : WindowBound) : Prop :=
  2 * output.lo ≤ scaledErrorTerm s - input.hi * twiceInvGoldenRatio ∧
    scaledErrorTerm s - input.lo * twiceInvGoldenRatio ≤ 2 * output.hi

/-- Consistency at a state is decided by comparisons in `ℤ√5`. -/
instance (s : State) (input output : WindowBound) : Decidable (ConsistentAt s input output) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `16 (r + 1 / φ² - z / φ)` as an element of `ℤ√5`, using `1 / φ² = (3 - √5) / 2`. -/
def scaledLowerBase (s : State) (r : ℕ) : ZSqrtFive :=
  ⟨16 * r + 24 + 8 * s.z, -8 - 8 * s.z⟩

/-- Proposition 24(ii) at a lower choice `r`, multiplied by 16, together with
the bound `w - r - |D| ≤ 2` on the diagonal discrepancy stated in Section 6.6:
`15 - 8√5 ≤ r + 1 / φ² - (z + hi(V)) / φ` and
`r + 1 / φ² - (z + lo(V)) / φ ≤ 13 - 4√5`. -/
def LowerChoiceBounds (s : State) (input : WindowBound) (r : ℕ) : Prop :=
  (⟨240, -128⟩ : ZSqrtFive) ≤ scaledLowerBase s r - input.hi * twiceInvGoldenRatio ∧
    scaledLowerBase s r - input.lo * twiceInvGoldenRatio ≤ ⟨208, -64⟩ ∧
    s.w - r - ((offsets s.D).card : ℤ) ≤ 2

/-- The lower-choice bounds are decided by comparisons in `ℤ√5` and `ℤ`. -/
instance (s : State) (input : WindowBound) (r : ℕ) : Decidable (LowerChoiceBounds s input r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Proposition 24(i) at one vertex, multiplied by 8:
`(19√5 - 49) / 8 ≤ lo(W)` and `hi(W) ≤ √5 - 1`. -/
def UpperBounds (bound : WindowBound) : Prop :=
  (⟨-49, 19⟩ : ZSqrtFive) ≤ bound.lo ∧ bound.hi ≤ ⟨-8, 8⟩

/-- Property (i) at one vertex is decided by comparisons in `ℤ√5`. -/
instance (bound : WindowBound) : Decidable (UpperBounds bound) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Section 4.3: the encoded twelve symbols ending after the first `k` symbols
of the queue, that is, a window of the word `H_in Q`. -/
def inputWindow (s : State) (k : ℕ) : ℕ :=
  (s.queue.take k).foldl destination s.input

/-- Section 4.3: every window of `H_in Q`, and `H_out`, is a vertex. -/
def checkStateHistories (s : State) : Bool :=
  (List.range (s.queue.length + 1)).all
      (fun k => (Data.historyGraph.lookup (inputWindow s k)).isSome) &&
    (Data.historyGraph.lookup s.output).isSome

/-- Proposition 24 at one state: its histories are vertices with window bounds,
the bounds are consistent at the state, and every lower choice of every branch
satisfies `LowerChoiceBounds`. -/
def checkWindowState (s : State) : Bool :=
  checkStateHistories s &&
    match windowBound? s.input, windowBound? s.output with
    | some input, some output =>
        decide (ConsistentAt s input output) &&
          match calculateChoices Data.historyGraph s with
          | .error _ => false
          | .ok choices => choices.all fun choice =>
              match choice.1 with
              | none => true
              | some r => decide (LowerChoiceBounds s input r)
    | _, _ => false

/-- Proposition 24 at one entry of the window-bound table: the key is a vertex,
it satisfies property (i) if its last symbol has column bit 1, and the witness
state has this vertex as its output history. -/
def checkWindowVertex (entry : ℕ × WindowBound) : Bool :=
  (Data.historyGraph.lookup entry.1).isSome &&
    (upperBit (entry.1 % 4) != 1 || decide (UpperBounds entry.2)) &&
    ((lookupStateIndex entry.2.witness Data.stateIndex).map State.output == some entry.1)

/-- Section 6.6: a history-graph entry has window bounds. -/
def hasWindowBound (entry : ℕ × ℕ) : Bool :=
  (windowBound? entry.1).isSome

end Queens.Finite
