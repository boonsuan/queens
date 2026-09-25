import Queens.LocalUpdates
import Queens.Finite.Branching

/-!
# The actual branch of the row search

The row-search loop of Algorithm 1 finds the first row whose temporary lower
record and actual upper-row bit are both zero. Queue extension is parameterized
by its semantic guarantee, separating graph/history bookkeeping from the loop.
-/

namespace Queens.Finite

/-- Reading a present symbol from an actual word segment agrees with the
absolute queen word, including the implementation's default-zero accessor. -/
theorem wordSegment_getD (m length r : ℕ) (hr : r < length) :
    ((wordSegment m length)[r]?.getD 0) = queenSymbol (m + r) := by
  have hlength : r < (wordSegment m length).length := by simpa using hr
  rw [List.getElem?_eq_getElem hlength]
  exact wordSegment_getElem _ _ _ hr

/-- The semantic guarantee required of queue extension: an actual segment
can be extended along the actual word to cover a request, without exceeding
the range whose symbols are already known. -/
def ExtendsActualWord (graph : HistoryGraph) (input m limit : ℕ)
    (memory : ℕ := historyLength) : Prop :=
  ∀ k request out, k ≤ limit → request ≤ limit →
    extendQueue graph input (wordSegment m k) (request : ℤ) (memory := memory) = .ok out →
      ∃ k', k ≤ k' ∧ request ≤ k' ∧ k' ≤ limit ∧ wordSegment m k' ∈ out

/-- A successful row search retains the first actual free row. This is the
operational row-search component of Section 5, Lemma 16; the queue extension
hypothesis is supplied separately from the actual history-graph path. -/
theorem findFreeRow_contains_actual {memory : ℕ} {graph : HistoryGraph}
    {input rows m limit target : ℕ}
    (hextends : ExtendsActualWord graph input m limit (memory := memory))
    (hfree : hasOffset rows target = false ∧ upperRowBit (m + target) = 0)
    (hblocked : ∀ r < target, hasOffset rows r = true ∨ upperRowBit (m + r) = 1)
    (htarget : target + 1 ≤ limit) {fuel start k : ℕ} {out : List (ℕ × List ℕ)}
    (hstart : start ≤ target) (hfuel : target < start + fuel) (hk : k ≤ limit)
    (hok : findFreeRow graph input rows fuel start (wordSegment m k) (memory := memory) = .ok out) :
    ∃ k', k ≤ k' ∧ target + 1 ≤ k' ∧ k' ≤ limit ∧
      (target, wordSegment m k') ∈ out := by
  induction fuel generalizing start k out with
  | zero => omega
  | succ fuel ih =>
    cases hex : extendQueue graph input (wordSegment m k) (start + 1 : ℤ) (memory := memory) with
    | error e => simp [findFreeRow, hex, Bind.bind, Except.bind] at hok
    | ok queues =>
      have hbranches : allBranches queues (fun queue =>
          if !hasOffset rows start ∧ rowBit (queue[start]?.getD 0) = 0 then
            .ok [(start, queue)]
          else findFreeRow graph input rows fuel (start + 1) queue (memory := memory)) =
          .ok out := by
        simpa [findFreeRow, hex, Bind.bind, Except.bind] using hok
      obtain ⟨k', hkk', hrequest, hk'limit, hqueue⟩ :=
        hextends k (start + 1) queues hk (by omega) (by simpa using hex)
      obtain ⟨branch, hbranch, hsubset⟩ := allBranches_branch hbranches hqueue
      have hread : rowBit ((wordSegment m k')[start]?.getD 0) = upperRowBit (m + start) := by
        rw [wordSegment_getD _ _ _ (by omega), rowBit_queenSymbol]
      by_cases heq : start = target
      · subst start
        have houtput : [(target, wordSegment m k')] = branch := by
          simpa [hread, hfree.1, hfree.2] using hbranch
        refine ⟨k', hkk', hrequest, hk'limit, hsubset _ ?_⟩
        rw [← houtput]
        simp
      · have hlt : start < target := by omega
        have hnotfree : ¬((!hasOffset rows start) = true ∧
            rowBit ((wordSegment m k')[start]?.getD 0) = 0) := by
          rw [hread]
          rcases hblocked start hlt with hmask | hbit
          · simp [hmask]
          · simp [hbit]
        have hrec : findFreeRow graph input rows fuel (start + 1) (wordSegment m k')
            (memory := memory) = .ok branch := by
          simpa only [if_neg hnotfree] using hbranch
        obtain ⟨k'', hk'k'', htargetk, hk''limit, hmem⟩ :=
          ih (by omega) (by omega) hk'limit hrec
        exact ⟨k'', by omega, htargetk, hk''limit, hsubset _ hmem⟩

end Queens.Finite
