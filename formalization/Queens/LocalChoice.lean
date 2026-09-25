import Queens.LocalSources
import Queens.Finite.RowSearch

/-!
# The actual branch of the candidate loop

Algorithm 1 tests lower candidates in increasing row order. This file proves
that every successful complete branching calculation retains the actual
greedy choice. Queue extension is supplied through `ExtendsActualWord`,
separating history-graph bookkeeping from the candidate-loop argument.
-/

namespace Queens

/-- Agreement of an optional finite-calculation choice with the actual queen.
`none` denotes an upper queen and `some r` denotes the lower row `m + r`. -/
def ChoiceMatches (n : ℕ) : Option ℕ → Prop
  | none => n < q n
  | some r => q n < n ∧ q n = rowReference n + r

/-- A matching optional choice is exactly the actual lower offset when the
queen is lower, and `none` otherwise. This normal form feeds the record updates. -/
theorem ChoiceMatches.eq_actual {n : ℕ} {choice : Option ℕ} (hmatch : ChoiceMatches n choice) :
    choice = if q n < n then some (rowOffset n) else none := by
  cases choice with
  | none =>
    have hupper : n < q n := hmatch
    rw [if_neg (by omega)]
  | some r =>
    obtain ⟨hlower, hrow⟩ := hmatch
    rw [if_pos hlower]
    congr 1
    unfold rowOffset
    omega

private theorem mask_tests_of_available {n r memory : ℕ} {s : Finite.State}
    (hrep : StateRepresented n s memory) (hn : 0 < n) (hr : (r : ℤ) ≤ window n)
    (havailable : Available n (rowReference n + r) (fun i => q i.val)) :
    Finite.hasOffset s.R r = false ∧
      Finite.hasOffset s.D (s.w - (r : ℤ)).toNat = false ∧
      Finite.hasOffset s.A r = false := by
  obtain ⟨hR, hD, hA, _, _⟩ := (available_candidate_iff hn hr).mp havailable
  rw [hrep.rowOffsets_eq] at hR
  rw [hrep.diagonalOffsets_eq, hrep.window_eq] at hD
  rw [hrep.antidiagonalOffsets_eq] at hA
  simpa only [Finite.mem_offsets, Bool.not_eq_true] using And.intro hR (And.intro hD hA)

/-- One successful iteration on an actual queue either retains this available
candidate, or retains a recursive continuation and this candidate is attacked.
This is the local operational step in the choice part of Lemma 16. -/
theorem chooseFrom_actual_step {memory : ℕ} {n remaining r k limit : ℕ}
    {s : Finite.State} {graph : Finite.HistoryGraph} {out : List Finite.Choice}
    (hrep : StateRepresented n s memory) (hn : 0 < n) (hcondition : Finite.Condition s)
    (hextends : Finite.ExtendsActualWord (memory := memory) graph s.input (rowReference n) limit)
    (hlimit : 5 ≤ limit) (hcausal : rowReference n + limit ≤ n)
    (hr : (r : ℤ) ≤ window n) (hk : k ≤ limit)
    (hok : Finite.chooseFrom (memory := memory) graph s (remaining + 1) r
      (wordSegment (rowReference n) k) = .ok out)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    (Available n (rowReference n + r) (fun i => q i.val) ∧
      ∃ k', k ≤ k' ∧ k' ≤ limit ∧ (some r, wordSegment (rowReference n) k') ∈ out) ∨
    (¬Available n (rowReference n + r) (fun i => q i.val) ∧
      ∃ k', k ≤ k' ∧ k' ≤ limit ∧ ∃ branch,
        Finite.chooseFrom (memory := memory) graph s remaining (r + 1)
          (wordSegment (rowReference n) k') = .ok branch ∧
        ∀ choice ∈ branch, choice ∈ out) := by
  have hmask (havailable : Available n (rowReference n + r) (fun i => q i.val)) :=
    mask_tests_of_available hrep hn hr havailable
  by_cases hblocked :
      (Finite.hasOffset s.R r || Finite.hasOffset s.D (s.w - r).toNat ||
        Finite.hasOffset s.A r) = true
  · right
    refine ⟨?_, k, le_rfl, hk, out, ?_, fun _ h => h⟩
    · intro havailable
      obtain ⟨hR, hD, hA⟩ := hmask havailable
      simp only [hR, hD, hA, Bool.or_false, Bool.false_eq_true] at hblocked
    · simpa only [Finite.chooseFrom, if_pos hblocked, Bind.bind, Except.bind] using hok
  · let request := (1 + max (r : ℤ) ((s.z + r) / 2)).toNat
    have hrequest_eq : (request : ℤ) = 1 + max (r : ℤ) ((s.z + r) / 2) := by
      dsimp [request]
      rw [Int.toNat_of_nonneg (by omega)]
    have hrw : (r : ℤ) ≤ s.w := by simpa only [hrep.window_eq] using hr
    have hmax := candidate_request_le_four hcondition.1 hcondition.2.2.1 hrw
    have hrequestLimit : request ≤ limit := by omega
    cases hex : Finite.extendQueue (memory := memory) graph s.input (wordSegment (rowReference n) k)
        (1 + max (r : ℤ) ((s.z + r) / 2)) with
    | error e =>
      simp only [Finite.chooseFrom, if_neg hblocked, hex, Bind.bind, Except.bind,
        reduceCtorEq] at hok
    | ok queues =>
      have hbranches : Finite.allBranches queues (fun queue =>
          if Finite.rowBit (queue[r]?.getD 0) = 0 ∧
              !Finite.antidiagonalAttack (memory := memory) s queue r then
            .ok [(some r, queue)]
          else Finite.chooseFrom (memory := memory) graph s remaining (r + 1) queue) = .ok out := by
        simpa only [Finite.chooseFrom, if_neg hblocked, hex, Bind.bind, Except.bind] using hok
      obtain ⟨k', hkk', hrequest, hk'limit, hqueue⟩ :=
        hextends k request queues hk hrequestLimit (by simpa only [hrequest_eq] using hex)
      obtain ⟨branch, hbranch, hsubset⟩ := Finite.allBranches_branch hbranches hqueue
      have hz : -4 ≤ upperDisplacement n := by
        rw [hrep.upperDisplacement_eq]
        exact hcondition.2.1
      have htests := hrep.candidate_tests_iff hn hr (show r < k' by omega) hz
        (show rowReference n + k' ≤ n by omega)
        (show (upperDisplacement n + (r : ℤ)) / 2 < k' by rw [hrep.upperDisplacement_eq]; omega)
      have hmasks : Finite.hasOffset s.R r = false ∧
          Finite.hasOffset s.D (s.w - (r : ℤ)).toNat = false ∧
          Finite.hasOffset s.A r = false := by
        simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using hblocked
      obtain ⟨hR, hD, hA⟩ := hmasks
      by_cases hclear : Finite.rowBit (((wordSegment (rowReference n) k')[r]?).getD 0) = 0 ∧
          (!Finite.antidiagonalAttack (memory := memory) s
            (wordSegment (rowReference n) k') r) = true
      · left
        have havailable : Available n (rowReference n + r) (fun i => q i.val) := by
          apply htests.mpr
          exact ⟨hR, hD, hA, hclear.1, by simpa using hclear.2⟩
        have houtput : [(some r, wordSegment (rowReference n) k')] = branch := by
          simpa only [if_pos hclear, Except.ok.injEq] using hbranch
        refine ⟨havailable, k', hkk', hk'limit, hsubset _ ?_⟩
        rw [← houtput]
        simp
      · right
        refine ⟨?_, k', hkk', hk'limit, branch, ?_, hsubset⟩
        · intro havailable
          have h := htests.mp havailable
          exact hclear ⟨h.2.2.2.1, by simp [h.2.2.2.2]⟩
        · simpa only [if_neg hclear] using hbranch

/-- A successful candidate loop retains the actual lower queen whenever
the searched interval reaches its offset and begins at or before it. Earlier
available candidates are excluded by the defining greedy minimality. -/
theorem chooseFrom_contains_actual_lower {memory : ℕ} {n target limit : ℕ}
    {s : Finite.State} {graph : Finite.HistoryGraph}
    (hrep : StateRepresented n s memory) (hn : 0 < n) (hcondition : Finite.Condition s)
    (hextends : Finite.ExtendsActualWord (memory := memory) graph s.input (rowReference n) limit)
    (hlimit : 5 ≤ limit) (hcausal : rowReference n + limit ≤ n)
    (htarget : (target : ℤ) ≤ window n) (hqueen : q n = rowReference n + target)
    {remaining start k : ℕ} {out : List Finite.Choice}
    (hstart : start ≤ target) (hremaining : target < start + remaining) (hk : k ≤ limit)
    (hok : Finite.chooseFrom (memory := memory) graph s remaining start
      (wordSegment (rowReference n) k) = .ok out)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    ∃ k', k ≤ k' ∧ k' ≤ limit ∧ (some target, wordSegment (rowReference n) k') ∈ out := by
  induction remaining generalizing start k out with
  | zero => omega
  | succ remaining ih =>
    have hstartWindow : (start : ℤ) ≤ window n := by omega
    rcases chooseFrom_actual_step hrep hn hcondition hextends hlimit hcausal
      hstartWindow hk hok with
      ⟨havailable, k', hkk', hk'limit, hmem⟩ |
      ⟨hblocked, k', hkk', hk'limit, branch, hbranch, hsubset⟩
    · have hle := q_le_of_available havailable
      have heq : start = target := by omega
      exact ⟨k', hkk', hk'limit, by simpa only [heq] using hmem⟩
    · have hne : start ≠ target := by
        intro heq
        apply hblocked
        simpa only [heq, ← hqueen] using q_available n
      obtain ⟨k'', hk'k'', hk''limit, hmem⟩ :=
        ih (by omega) (by omega) hk'limit hbranch
      exact ⟨k'', by omega, hk''limit, hsubset _ hmem⟩

/-- If the actual queen is upper, every tested lower candidate is attacked.
A successful loop therefore retains the upper choice and its actual queue. -/
theorem chooseFrom_contains_actual_upper {memory : ℕ} {n limit : ℕ}
    {s : Finite.State} {graph : Finite.HistoryGraph}
    (hrep : StateRepresented n s memory) (hn : 0 < n) (hcondition : Finite.Condition s)
    (hextends : Finite.ExtendsActualWord (memory := memory) graph s.input (rowReference n) limit)
    (hlimit : 5 ≤ limit) (hcausal : rowReference n + limit ≤ n) (hupper : n < q n)
    {remaining start k : ℕ} {out : List Finite.Choice}
    (hwindow : ∀ r, start ≤ r → r < start + remaining → (r : ℤ) ≤ window n)
    (hk : k ≤ limit)
    (hok : Finite.chooseFrom (memory := memory) graph s remaining start
      (wordSegment (rowReference n) k) = .ok out)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    ∃ k', k ≤ k' ∧ k' ≤ limit ∧ (none, wordSegment (rowReference n) k') ∈ out := by
  induction remaining generalizing start k out with
  | zero =>
    have hout : [(none, wordSegment (rowReference n) k)] = out := by
      simpa only [Finite.chooseFrom, Except.ok.injEq] using hok
    exact ⟨k, le_rfl, hk, by simp only [← hout, List.mem_singleton]⟩
  | succ remaining ih =>
    have hstartWindow := hwindow start le_rfl (by omega)
    rcases chooseFrom_actual_step hrep hn hcondition hextends hlimit hcausal
      hstartWindow hk hok with
      ⟨havailable, _⟩ | ⟨_, k', hkk', hk'limit, branch, hbranch, hsubset⟩
    · have hle := q_le_of_available havailable
      have hrow := candidate_row_lt hstartWindow
      omega
    · obtain ⟨k'', hk'k'', hk''limit, hmem⟩ :=
        ih (fun r hrstart hrend => hwindow r (by omega) (by omega)) hk'limit hbranch
      exact ⟨k'', by omega, hk''limit, hsubset _ hmem⟩

/-- **Lemma 16, candidate choice.** Starting at offset zero and testing the
whole candidate window, the successful branching calculation contains a
choice matching the actual greedy queen and an actual extended queue. -/
theorem chooseFrom_contains_actual {memory : ℕ} {n k limit : ℕ}
    {s : Finite.State} {graph : Finite.HistoryGraph} {out : List Finite.Choice}
    (hrep : StateRepresented n s memory) (hn : 0 < n) (hcondition : Finite.Condition s)
    (hextends : Finite.ExtendsActualWord (memory := memory) graph s.input (rowReference n) limit)
    (hlimit : 5 ≤ limit) (hcausal : rowReference n + limit ≤ n) (hk : k ≤ limit)
    (hok : Finite.chooseFrom (memory := memory) graph s (s.w + 1).toNat 0
      (wordSegment (rowReference n) k) = .ok out)
    (hmemory : 12 ≤ memory := by first | assumption | decide) :
    ∃ choice k', k ≤ k' ∧ k' ≤ limit ∧ ChoiceMatches n choice ∧
      (choice, wordSegment (rowReference n) k') ∈ out := by
  by_cases hlower : q n < n
  · have htarget := rowOffset_le_window hlower
    have hqueen : q n = rowReference n + rowOffset n :=
      (Nat.add_sub_of_le (rowReference_le_q n)).symm
    have hremaining : rowOffset n < 0 + (s.w + 1).toNat := by
      rw [hrep.window_eq] at htarget
      omega
    obtain ⟨k', hkk', hk'limit, hmem⟩ := chooseFrom_contains_actual_lower hrep hn hcondition
      hextends hlimit hcausal htarget hqueen (Nat.zero_le _) hremaining hk hok
    exact ⟨some (rowOffset n), k', hkk', hk'limit, ⟨hlower, hqueen⟩, hmem⟩
  · have hupper : n < q n := by have := q_ne_self hn; omega
    have hwindow : ∀ r : ℕ, 0 ≤ r → r < 0 + (s.w + 1).toNat → (r : ℤ) ≤ window n := by
      intro r _ hr
      rw [hrep.window_eq]
      omega
    obtain ⟨k', hkk', hk'limit, hmem⟩ := chooseFrom_contains_actual_upper hrep hn hcondition
      hextends hlimit hcausal hupper hwindow hk hok
    exact ⟨none, k', hkk', hk'limit, hupper, hmem⟩

end Queens
