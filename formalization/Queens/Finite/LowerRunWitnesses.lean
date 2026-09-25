import Queens.LowerRuns

/-!
# Actual initial lower runs and repeated-run witnesses

For Corollary 19, a checked interval table identifies the first 1100 terms of
A275885 from actual greedy queens. It supplies both the initial cases before the
forty-symbol graph applies and attainment of every value claimed for A275887.
All finite assertions are reduced by the Lean kernel.
-/

namespace Queens.Finite

set_option Elab.async false

/-- Corollary 19: proposed start of the `k`th lower run in the checked prefix. -/
def witnessLowerRunStart (k : ℕ) : ℕ :=
  ((indexedLookup k lowerRunWitnessIntervalTree).getD (0, 0)).1

/-- Corollary 19: proposed upper endpoint of the `k`th lower run. -/
def witnessLowerRunEnd (k : ℕ) : ℕ := ((indexedLookup k lowerRunWitnessIntervalTree).getD (0, 0)).2

/-- Corollary 19: the lower-run length computed from the proposed interval. -/
def witnessLowerRunLength (k : ℕ) : ℕ := witnessLowerRunEnd k - witnessLowerRunStart k

/-- Corollary 19: the search for the next lower run begins at the preceding
upper endpoint, or at the origin for the first run. -/
def witnessLowerRunBase (k : ℕ) : ℕ := if k = 0 then 0 else witnessLowerRunEnd (k - 1)

/-- Corollary 19: a proposed interval is the first nonempty lower block after
its search base, with its upper endpoint verified inside the greedy prefix. -/
def CheckLowerRunInterval (k : ℕ) : Prop :=
  witnessLowerRunBase k ≤ witnessLowerRunStart k ∧
  witnessLowerRunStart k < witnessLowerRunEnd k ∧ witnessLowerRunEnd k < 5000 ∧
  (∀ i : Fin (witnessLowerRunStart k - witnessLowerRunBase k),
    runWitnessUpper (witnessLowerRunBase k + i.val)) ∧
  (∀ i : Fin (witnessLowerRunEnd k - witnessLowerRunStart k),
    runWitnessLower (witnessLowerRunStart k + i.val)) ∧
  runWitnessUpper (witnessLowerRunEnd k)

/-- The finite interval certificate is decidable. -/
instance (k : ℕ) : Decidable (CheckLowerRunInterval k) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: every proposed initial lower-run interval is checked directly
against the already certified greedy rows. -/
theorem lowerRunWitnessIntervals_checked : ∀ k : Fin 1100, CheckLowerRunInterval k.val := by
  decide +kernel

private theorem interval_eq_next (k : ℕ) (hk : k < 1100) :
    nextLowerColumn (witnessLowerRunBase k) = witnessLowerRunStart k ∧
    nextUpperColumn (witnessLowerRunStart k) = witnessLowerRunEnd k := by
  obtain ⟨hbase, hse, hend, hu, hl, he⟩ := lowerRunWitnessIntervals_checked ⟨k, hk⟩
  dsimp only at hbase hse hend hu hl he
  have hlower {n : ℕ} (hs : witnessLowerRunStart k ≤ n) (he' : n < witnessLowerRunEnd k) :
      q n < n := by
    have h := hl ⟨n - witnessLowerRunStart k, by omega⟩
    have heq : witnessLowerRunStart k + (n - witnessLowerRunStart k) = n := by omega
    dsimp only at h
    rw [heq] at h
    simpa [runWitnessLower, ← q_eq_runWitnessRow (by omega : n < 5000)] using h
  have hupper {n : ℕ} (hb : witnessLowerRunBase k ≤ n) (hs : n < witnessLowerRunStart k) :
      IsUpperColumnWithOrigin n := by
    have h := hu ⟨n - witnessLowerRunBase k, by omega⟩
    have heq : witnessLowerRunBase k + (n - witnessLowerRunBase k) = n := by omega
    dsimp only at h
    rw [heq] at h
    simpa [runWitnessUpper, IsUpperColumnWithOrigin,
      ← q_eq_runWitnessRow (by omega : n < 5000)] using h
  constructor
  · apply Nat.le_antisymm (nextLowerColumn_le hbase (hlower le_rfl hse))
    by_contra hlt
    have hb := le_nextLowerColumn (witnessLowerRunBase k)
    have hu' := hupper hb (by omega)
    exact (not_upperColumnWithOrigin_iff _).mpr (nextLowerColumn_lower _) hu'
  · have huend : IsUpperColumnWithOrigin (witnessLowerRunEnd k) := by
      simpa [runWitnessUpper, IsUpperColumnWithOrigin, ← q_eq_runWitnessRow hend] using he
    apply Nat.le_antisymm (nextUpperColumn_le (by omega) huend)
    by_contra hlt
    have hs := le_nextUpperColumn (witnessLowerRunStart k)
    have hl' := hlower hs (by omega)
    exact (not_upperColumnWithOrigin_iff _).mpr hl' (nextUpperColumn_upper _)

/-- Corollary 19: the finite intervals are exactly the initial intervals in the
canonical infinite lower-run enumeration; no graph path is used as an occurrence. -/
theorem lowerRun_interval_eq_witness {k : ℕ} (hk : k < 1100) :
    lowerRunStart k = witnessLowerRunStart k ∧ lowerRunEnd k = witnessLowerRunEnd k := by
  induction k with
  | zero =>
    have h := interval_eq_next 0 hk
    have hs : lowerRunStart 0 = witnessLowerRunStart 0 := by
      simpa [lowerRunStart, witnessLowerRunBase] using h.1
    exact ⟨hs, by simpa [lowerRunEnd, hs] using h.2⟩
  | succ k ih =>
    have hprev := ih (by omega)
    have h := interval_eq_next (k + 1) hk
    have hs : lowerRunStart (k + 1) = witnessLowerRunStart (k + 1) := by
      change nextLowerColumn (lowerRunEnd k) = witnessLowerRunStart (k + 1)
      rw [hprev.2]
      simpa [witnessLowerRunBase] using h.1
    exact ⟨hs, by simpa [lowerRunEnd, hs] using h.2⟩

/-- Corollary 19: the first 1100 actual terms of A275885 agree with the checked
finite interval table. -/
theorem lowerRunLength_eq_witness {k : ℕ} (hk : k < 1100) :
    lowerRunLength k = witnessLowerRunLength k := by
  obtain ⟨hs, he⟩ := lowerRun_interval_eq_witness hk
  simp [lowerRunLength, witnessLowerRunLength, hs, he]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: the twenty-third lower run ends at column 80, so subsequent
run-graph edges lie entirely in the forty-symbol verification. -/
theorem lowerRunEnd_twentyTwo : lowerRunEnd 22 = 80 := by
  rw [(lowerRun_interval_eq_witness (by decide : 22 < 1100)).2]
  decide +kernel

/-- Corollary 19: actual starting term indices witnessing each permitted
length of a maximal run of equal A275885 terms. -/
def repeatedRunWitnessStart (length : ℕ) : ℕ :=
  [0, 15, 0, 61, 28, 6, 42, 122, 348, 1053, 0, 446][length]?.getD 0

/-- Corollary 19: the repeated A275885 term at each chosen occurrence. -/
def repeatedRunWitnessLabel (length : ℕ) : ℕ :=
  [0, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 1][length]?.getD 0

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: all ten claimed repetition lengths occur in the actual-prefix
run sequence, with both unequal neighboring terms checked where required. -/
theorem repeatedRunWitnesses_checked : ∀ l : Fin 12,
    0 < l.val → l.val ≠ 10 →
      repeatedRunWitnessStart l.val + l.val < 1100 ∧
      Sequence.MaximalRun (fun k => witnessLowerRunLength k = repeatedRunWitnessLabel l.val)
        (repeatedRunWitnessStart l.val) l.val := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: every maximal repeated-term run starting before term 24 ends
with a permitted length within the checked prefix. This includes all runs whose
left boundary precedes the forty-symbol graph's applicability. -/
theorem earlyRepeatedRuns_checked : ∀ s : Fin 24, ∀ c : Fin 4,
    witnessLowerRunLength s.val = c.val →
    (s.val = 0 ∨ witnessLowerRunLength (s.val - 1) ≠ c.val) →
    ∃ l : Fin 12, 0 < l.val ∧ l.val ≠ 10 ∧ s.val + l.val < 1100 ∧
      Sequence.MaximalRun (fun k => witnessLowerRunLength k = c.val) s.val l.val := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: no initial block of twelve A275885 terms is constant. Together
with the later graph bound this excludes an infinite constant final run. -/
theorem earlyNoTwelve_checked : ∀ s : Fin 23, ∀ c : Fin 4,
    ¬∀ i : Fin 12, witnessLowerRunLength (s.val + i.val) = c.val := by
  decide +kernel

end Queens.Finite
