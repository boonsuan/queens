import Queens.Finite.RunWitnessData
import Queens.Runs

/-!
# Checked occurrence witnesses for Corollary 19

The graph bounds alone do not prove that any permitted value occurs. This file
checks actual greedy queens through column 4999 using the proved bitboard
checker. Every witness includes both endpoints needed for maximality or a gap.
The origin is counted as upper, exactly as in Corollary 19.
-/

namespace Queens.Finite

set_option Elab.async false

/-- Corollary 19: access the proposed finite row certificate. -/
def runWitnessRow (n : ℕ) : ℕ := (indexedLookup n runWitnessRowTree).getD 0

/-- Corollary 19: upper columns of the finite certificate, including the origin. -/
def runWitnessUpper (n : ℕ) : Prop := n = 0 ∨ n < runWitnessRow n

/-- Upper-column membership in the finite witness prefix is decidable. -/
instance (n : ℕ) : Decidable (runWitnessUpper n) := inferInstanceAs (Decidable (_ ∨ _))

/-- Corollary 19: lower columns of the finite certificate. -/
def runWitnessLower (n : ℕ) : Prop := runWitnessRow n < n

/-- Lower-column membership in the finite witness prefix is decidable. -/
instance (n : ℕ) : Decidable (runWitnessLower n) := inferInstanceAs (Decidable (_ < _))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: the complete finite prefix is certified by the defining greedy
rule. The checker is executable, while its refinement to `q` is kernel-proved. -/
theorem runWitnessRows_checked :
    runWitnessRows.length = 5000 ∧ AttackBoard.empty.checkRows runWitnessRows = true := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19: the fast row lookup is a faithful layout of the same
sequential row certificate. Only a linear list comparison is needed. -/
theorem runWitnessRowTree_checked :
    indexedAll (fun e => decide (indexedLookup e.1 runWitnessRowTree = some e.2))
      runWitnessRowTree = true ∧
    indexedEntries runWitnessRowTree = runWitnessRows.zipIdx.map Prod.swap := by
  decide +kernel

/-- Corollary 19: every checked witness row is the actual greedy queen row. -/
theorem q_eq_runWitnessRow {n : ℕ} (hn : n < 5000) : q n = runWitnessRow n := by
  have hn' : n < runWitnessRows.length := by rw [runWitnessRows_checked.1]; exact hn
  have hself : ∀ e ∈ indexedEntries runWitnessRowTree,
      indexedLookup e.1 runWitnessRowTree = some e.2 := by
    intro e he
    exact of_decide_eq_true (indexedAll_eq_true.mp runWitnessRowTree_checked.1 e he)
  have halign : (indexedEntries runWitnessRowTree).map (fun e => (e.1, e.2)) =
      runWitnessRows.zipIdx.map Prod.swap := by simpa using runWitnessRowTree_checked.2
  obtain ⟨a, hlookup, ha⟩ := indexedLookup_of_list_alignment (field := id) hself halign hn'
  have h := AttackBoard.empty_represents.q_eq_of_checkRows runWitnessRows_checked.2 ⟨n, hn'⟩
  dsimp only [id] at ha
  simpa [runWitnessRow, hlookup, ha] using h

/-- Corollary 19: starts of actual lower-column runs of each length 1, 2, 3. -/
def lowerRunWitnessStart (length : ℕ) : ℕ := [0, 12, 3, 4970][length]?.getD 0

/-- Corollary 19: starts of actual upper-column runs of each length 1 through 5. -/
def upperRunWitnessStart (length : ℕ) : ℕ := [0, 11, 31, 0, 5, 43][length]?.getD 0

/-- Corollary 19: starts of actual upper-column gaps of each length 1 through 4. -/
def upperGapWitnessStart (gap : ℕ) : ℕ := [0, 0, 11, 2, 4969][gap]?.getD 0

/-- Corollary 19: starts of actual lower-column gaps of each length 1 through 6. -/
def lowerGapWitnessStart (gap : ℕ) : ℕ := [0, 3, 10, 30, 33, 4, 42][gap]?.getD 0

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the entire finite certificate at this declaration.
/-- Corollary 19, four basic attainment assertions: each listed length occurs
with verified boundary columns in the actual-prefix certificate. -/
theorem basicRunWitnesses_checked :
    (∀ l : Fin 4, 0 < l.val → lowerRunWitnessStart l.val + l.val < 5000 ∧
      Sequence.MaximalRun runWitnessLower (lowerRunWitnessStart l.val) l.val) ∧
    (∀ l : Fin 6, 0 < l.val → upperRunWitnessStart l.val + l.val < 5000 ∧
      Sequence.MaximalRun runWitnessUpper (upperRunWitnessStart l.val) l.val) ∧
    (∀ l : Fin 5, 0 < l.val → upperGapWitnessStart l.val + l.val < 5000 ∧
      Sequence.ConsecutiveGap runWitnessUpper (upperGapWitnessStart l.val) l.val) ∧
    (∀ l : Fin 7, 0 < l.val → lowerGapWitnessStart l.val + l.val < 5000 ∧
      Sequence.ConsecutiveGap runWitnessLower (lowerGapWitnessStart l.val) l.val) := by
  decide +kernel

end Queens.Finite
