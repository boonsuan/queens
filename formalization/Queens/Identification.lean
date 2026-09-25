import Queens.Main
import Queens.Finite.Certificate
import Queens.Finite.Seed

/-!
# Following the actual queens forever

This file formalizes the induction of Section 6.4 and its deduction of Lemma 5
and Theorem 1. The one-step correspondence of Lemma 16 is stated explicitly as
`LocalStepExact` and is proved in `Queens.Exactness`. This separates the infinite
induction from the operational details of the local calculation.

All other inputs are proved: the seed is the actual board, the finite invariant
is closed, its states satisfy Condition 15, and actual records satisfying those
bounds give the required discrepancy. The induction tracks the queen word as well
as the represented state, because input requests use the previously verified word.
-/

namespace Queens

/-- The precise one-step correspondence of **Lemma 16**. If all branches
of the finite calculation succeed, its successor list contains the actual next
state, and its checked output extends the actual word's path in the history graph.
The universal success hypothesis is supplied by Proposition 17 in the induction;
it is not claimed to follow from Condition 15 alone. -/
def LocalStepExact : Prop :=
  ∀ (n : ℕ), 30 ≤ n → ∀ (s : Finite.State) (next : List Finite.State),
    StateRepresented n s → Finite.Condition s →
    Finite.Data.historyGraph.FollowsThrough queenSymbol (n - 1) →
    Finite.calculate Finite.Data.historyGraph s = .ok next →
    ∃ t ∈ next, StateRepresented (n + 1) t ∧
      Finite.Data.historyGraph.FollowsThrough queenSymbol n

/-- The three simultaneous assertions in the induction of Section 6.4:
the state represents the actual board, belongs to the finite invariant, and the
already determined queen word follows the history graph. -/
def ActualInvariant (n : ℕ) : Prop :=
  ∃ s, StateRepresented n s ∧ Finite.Certified s ∧
    Finite.Data.historyGraph.FollowsThrough queenSymbol (n - 1)

/-- The verified starting board establishes all three assertions at column 30
(Section 6.1 and the base case of Section 6.4). -/
theorem actualInvariant_thirty : ActualInvariant 30 :=
  ⟨Finite.initialState, Finite.initialState_represented,
    Finite.initialState_certified, Finite.queenWord_follows_through_twentyNine⟩

/-- The induction step of Section 6.4, conditional only on the explicitly
stated one-step correspondence. The finite checker supplies all successor bounds. -/
theorem ActualInvariant.succ (hexact : LocalStepExact) {n : ℕ} (hn : 30 ≤ n)
    (hinv : ActualInvariant n) : ActualInvariant (n + 1) := by
  obtain ⟨s, hrep, hcert, hword⟩ := hinv
  obtain ⟨next, hnext, hall⟩ := Finite.certified_successors hcert
  obtain ⟨t, ht, hrep', hword'⟩ :=
    hexact n hn s next hrep (Finite.certified_condition hcert) hword hnext
  exact ⟨t, hrep', hall t ht, by simpa using hword'⟩

/-- The complete infinite induction of Section 6.4. Its hypothesis is precisely
the separately proved semantic correspondence in `LocalStepExact`. -/
theorem actualInvariant_of_localStepExact (hexact : LocalStepExact)
    (n : ℕ) (hn : 30 ≤ n) : ActualInvariant n := by
  induction n, hn using Nat.le_induction with
  | base => exact actualInvariant_thirty
  | succ n hn ih => exact ih.succ hexact hn

/-- The local record's next rank agrees with the positive chronological rank
at a lower column. This connects equation (local-rank) to Lemma 5. -/
theorem nextLowerRank_lowerColumn (k : ℕ) :
    nextLowerRank (lowerColumn k) = k + 1 := by
  classical
  unfold nextLowerRank earlierLowerColumns
  rw [← Nat.count_eq_card_filter_range]
  exact congrArg (fun j => j + 1)
    (Nat.count_nth_of_infinite (infinite_lowerColumns q_surjective) k)

/-- **Lemma 5**, conditional on one-step exactness. Early columns use the direct
greedy prefix check; later columns use the represented, certified state. -/
theorem diagonalDiscrepancy_of_localStepExact (hexact : LocalStepExact) :
    DiagonalDiscrepancy 4 := by
  intro k
  have hlower := lowerColumn_lower (infinite_lowerColumns q_surjective) k
  rw [lowerDiagonal_cast]
  by_cases hprefix : lowerColumn k < 30
  · have h := Finite.prefix_discrepancy hprefix hlower
    have hcount : ((Finset.range (lowerColumn k + 1)).filter (fun i => q i < i)).card =
        k + 1 := by
      classical
      rw [← Nat.count_eq_card_filter_range]
      exact Nat.count_nth_succ_of_infinite (infinite_lowerColumns q_surjective) k
    rw [hcount] at h
    exact_mod_cast h
  · obtain ⟨s, hrep, hcert, _⟩ :=
      actualInvariant_of_localStepExact hexact (lowerColumn k) (by omega)
    have h := discrepancy_of_represented_condition hrep.toRecordsRepresented
      (Finite.certified_condition hcert) hlower
    rw [nextLowerRank_lowerColumn] at h
    exact_mod_cast h

/-- **Theorem 1**, conditional on the single local semantic obligation of
Lemma 16. The finite verification and all mathematical deductions are proved. -/
theorem main_of_localStepExact (hexact : LocalStepExact) (n : ℕ) :
    (n < q n → |(q n : ℝ) - (n : ℝ) * Real.goldenRatio| < 5 / Real.goldenRatio) ∧
    (q n < n → |(q n : ℝ) - (n : ℝ) / Real.goldenRatio| < 4 + 5 / Real.goldenRatio) :=
  main_of_diagonalDiscrepancy (diagonalDiscrepancy_of_localStepExact hexact) n

end Queens
