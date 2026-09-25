import Queens.LocalRequests
import Queens.LocalGeometry
import Queens.Finite.RowSearch
import Queens.Finite.Seed

/-!
# Causal bounds for the actual branch

Lemma 16 uses `κ ≥ 12` and Condition 15 to show that every requested symbol
precedes the current column. The verified starting board and monotonicity of
the actual row reference establish the lower bound on `κ` for all later columns.
-/

namespace Queens

/-- The actual upper-count reference never decreases as the board grows.
This propagates the starting inequality `κ ≥ 12` in Section 6.4. -/
theorem countReference_mono : Monotone countReference := by
  intro i j hij
  exact upperCount_mono (Nat.sub_le_sub_right (rowReference_mono hij) 1)

/-- The starting row reference is 19, and later row references are no smaller.
Thus all later twelve-symbol input histories have positive indices. -/
theorem rowReference_ge_nineteen {n : ℕ} (hn : 30 ≤ n) : 19 ≤ rowReference n := by
  have h := rowReference_mono hn
  rwa [Finite.rowReference_thirty] at h

/-- The upper-count reference stays at least twelve after the verified start,
as required by Lemma 16. -/
theorem countReference_ge_twelve {n : ℕ} (hn : 30 ≤ n) : 12 ≤ countReference n := by
  have h := countReference_mono hn
  rwa [Finite.countReference_thirty] at h

/-- Under Condition 15 and `κ ≥ 12`, every symbol through offset six is already
determined. This is the strict causality inequality of Lemma 16(i), independent
of the history length used in the forty-symbol extension of Corollary 19. -/
theorem StateRepresented.requests_causal_general {memory n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s (memory := memory))
    (hcount : 12 ≤ countReference n) (hc : Finite.Condition s) :
    rowReference n + 6 < n := by
  apply request_before_current_column hcount
  change -4 ≤ upperDisplacement n
  rw [hrep.upperDisplacement_eq]
  exact hc.2.1

/-- Lemma 16(i): the checked starting board supplies the count bound needed
for causality in the twelve-symbol calculation from column 30 onwards. -/
theorem StateRepresented.requests_causal {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s) (hn : 30 ≤ n) (hc : Finite.Condition s) :
    rowReference n + 6 < n :=
  hrep.requests_causal_general (countReference_ge_twelve hn) hc

/-- The actual history graph path supplies the queue-extension guarantee
used by the executable candidate and row-search loops (Lemma 16(i)). The history
length and graph are arbitrary, as required by Corollary 19's larger graph. -/
theorem StateRepresented.extendsActualWord_general {memory n : ℕ} {s : Finite.State}
    {graph : Finite.HistoryGraph} (hrep : StateRepresented n s (memory := memory))
    (hstart : memory < rowReference n)
    (hword : graph.FollowsThrough queenSymbol (n - 1) (memory := memory)) :
    Finite.ExtendsActualWord graph s.input (rowReference n) (n - rowReference n)
      (memory := memory) := by
  intro k request out hk hrequest hok
  have hmn : rowReference n ≤ n := by have := hrep.queue_before_column; omega
  have hinput : s.input = inputHistoryAt (rowReference n) (memory := memory) :=
    hrep.input_eq.symm
  rw [hinput] at hok
  have hmem := extendQueue_contains_actual (request := (request : ℤ))
    hstart (by simp only [Int.toNat_natCast]; omega) hword hok
  refine ⟨max k request, Nat.le_max_left _ _, Nat.le_max_right _ _, by omega, ?_⟩
  simpa using hmem

/-- Lemma 16(i): queue extension along the checked twelve-symbol graph retains
the actual word after the verified starting column. -/
theorem StateRepresented.extendsActualWord {n : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s) (hn : 30 ≤ n)
    (hword : Finite.Data.historyGraph.FollowsThrough queenSymbol (n - 1)) :
    Finite.ExtendsActualWord Finite.Data.historyGraph s.input (rowReference n)
      (n - rowReference n) := by
  have hm := rowReference_ge_nineteen hn
  exact hrep.extendsActualWord_general (by dsimp [Finite.historyLength]; omega) hword

end Queens
