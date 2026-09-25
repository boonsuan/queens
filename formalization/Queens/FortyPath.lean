import Queens.GeneralExactness
import Queens.Finite.FortyCertificate
import Queens.Finite.FortySeed

/-!
# The actual path in the forty-symbol state graph

Corollary 19's refined graph must describe the actual infinite greedy process.
This file repeats the simultaneous induction of Section 6.4 from the checked
board before column 80, using the generic longer-history version of Lemma 16.
It retains an indexed path, rather than just separate membership witnesses,
so that Appendix A's contractions apply to consecutive actual states.
-/

namespace Queens.Finite.Forty

/-- Corollary 19: an indexed state at time `j` represents the board before
column `80 + j`, with the earlier actual word following the forty-symbol graph. -/
def RepresentsAt (j : ℕ) (v : Vertex) : Prop :=
  StateRepresented (80 + j) (state v) 40 ∧
    FortyData.historyGraph.FollowsThrough queenSymbol (79 + j) 40

/-- Corollary 19: the checked seed establishes the refined invariant at
vertex zero, before column eighty. -/
theorem representsAt_zero :
    RepresentsAt 0 ⟨0, by rw [data_sizes.2.2.1]; omega⟩ := by
  constructor
  · simpa only [Nat.add_zero, ← initialState_eq_state_zero] using initialState_represented
  · simpa only [Nat.add_zero] using queenWord_follows_through_seventyNine

/-- Corollary 19: every represented refined state has an indexed successor
representing the actual next board. No arbitrary graph path is substituted
for the greedy sequence in this induction. -/
theorem RepresentsAt.next {j : ℕ} {v : Vertex} (h : RepresentsAt j v) :
    ∃ w : Vertex, w.val ∈ successorIndices v ∧ RepresentsAt (j + 1) w := by
  obtain ⟨next, hnext, hexact⟩ := calculated_successors v
  have hm : 40 < rowReference (80 + j) := by
    have hmono := rowReference_mono (show 80 ≤ 80 + j by omega)
    rw [rowReference_eighty] at hmono
    omega
  have hk : 12 ≤ countReference (80 + j) := by
    have hmono := countReference_mono (show 80 ≤ 80 + j by omega)
    rw [countReference_eighty] at hmono
    omega
  have hword : FortyData.historyGraph.FollowsThrough queenSymbol (80 + j - 1) 40 := by
    simpa only [show 80 + j - 1 = 79 + j by omega] using h.2
  obtain ⟨t, ht, hrep, hword'⟩ := local_step_exact_of_memory
    (by decide : 12 ≤ 40) hm hk historyGraph_wellFormed h.1 (state_condition v) hword hnext
  obtain ⟨w, hw, hwt⟩ := (hexact t).mp ht
  refine ⟨w, hw, ?_, ?_⟩
  · simpa only [hwt, Nat.add_assoc] using hrep
  · simpa only [show 79 + (j + 1) = 80 + j by omega] using hword'

private noncomputable def actualVertexWithProof : (j : ℕ) → {v : Vertex // RepresentsAt j v}
  | 0 => ⟨⟨0, by rw [data_sizes.2.2.1]; omega⟩, representsAt_zero⟩
  | j + 1 =>
      let h := (actualVertexWithProof j).property.next
      ⟨Classical.choose h, (Classical.choose_spec h).2⟩

/-- Corollary 19: an indexed infinite path following the actual greedy board,
with time zero immediately before column 80. -/
noncomputable def actualVertex (j : ℕ) : Vertex := (actualVertexWithProof j).val

/-- Corollary 19: each vertex of the selected path faithfully represents its
actual board and all earlier forty-symbol word windows. -/
theorem actualVertex_represents (j : ℕ) : RepresentsAt j (actualVertex j) :=
  (actualVertexWithProof j).property

/-- Appendix A: consecutive vertices of the actual path are connected by a
checked edge of the refined state graph. -/
theorem actualVertex_step (j : ℕ) :
    (actualVertex (j + 1)).val ∈ successorIndices (actualVertex j) :=
  (Classical.choose_spec (actualVertexWithProof j).property.next).1

/-- Appendix A: the output label of the indexed path is the actual column
bit. Time zero records column 79, and each subsequent edge records the next
column, giving the precise indexing needed when contracting lower runs. -/
theorem actualVertex_output (j : ℕ) :
    upperBit ((state (actualVertex j)).output % 4) = columnBit (79 + j) := by
  have h := (actualVertex_represents j).1.output_last (by decide) (by omega)
  rw [h, upperBit_queenSymbol]
  congr 1
  omega

end Queens.Finite.Forty
