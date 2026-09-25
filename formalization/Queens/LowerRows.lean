import Queens.Greedy
import Mathlib.Data.Nat.Nth

/-!
# Sorted lower rows

Section 2 distinguishes chronological lower rows from their increasing enumeration.
This file proves Lemma 4: the sorted row of positive rank `j` is `j + U(j - 1)`.
Lean uses zero-based indices, so the formula below is `k + 1 + U(k)`.

The characterization of the complement of the upper rows uses only Lemma 2.
Identifying that complement with occupied lower rows additionally uses the permutation
property (Lemma 3), passed explicitly to the lemmas in this file.
-/

namespace Queens

/-- A row occupied by a lower queen, as in Section 2. -/
def IsLowerRow (r : ℕ) : Prop := ∃ n, q n < n ∧ q n = r

/-- The lower rows in increasing order. This is `vⱼ` in Section 2, with Lean index
`k` corresponding to the paper's positive index `j = k + 1`. -/
noncomputable def sortedLowerRow (k : ℕ) : ℕ := Nat.nth IsLowerRow k

private noncomputable def rowFormula (k : ℕ) : ℕ := k + 1 + upperCount k

private lemma rowFormula_strictMono : StrictMono rowFormula := by
  intro i j hij
  have hcount := upperCount_mono hij.le
  dsimp [rowFormula]
  omega

private lemma rowFormula_not_upper (k n : ℕ) (hn : n < q n) :
    q n ≠ rowFormula k := by
  have hrow := q_eq_add_upperCount hn
  by_cases hnk : n ≤ k
  · have hcount := upperCount_mono hnk
    dsimp [rowFormula]
    omega
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp only [Nat.succ_eq_add_one] at hrow
    have hcount := upperCount_mono (show k ≤ i by omega)
    have hstep := upperCount_succ i
    rw [if_pos hn] at hstep
    dsimp [rowFormula]
    omega

private lemma rowFormula_lower (hsurj : Function.Surjective q) (k : ℕ) :
    IsLowerRow (rowFormula k) := by
  obtain ⟨n, hn⟩ := hsurj (rowFormula k)
  refine ⟨n, ?_, hn⟩
  have hnpos : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    simp only [q_zero, rowFormula] at hn
    omega
  have hneq := q_ne_self hnpos
  have hnot : ¬ n < q n := fun h => rowFormula_not_upper k n h hn
  omega

private lemma lowerRow_in_range_rowFormula {r : ℕ} (hr : IsLowerRow r) :
    r ∈ Set.range rowFormula := by
  obtain ⟨n, hn, rfl⟩ := hr
  have hpos : 0 < q n := by
    have hne : q n ≠ 0 := by
      intro heq
      have := q_injective (heq.trans q_zero.symm)
      omega
    omega
  have hex : ∃ k, q n ≤ rowFormula k := ⟨q n, by dsimp [rowFormula]; omega⟩
  let k := Nat.find hex
  have hle : q n ≤ rowFormula k := Nat.find_spec hex
  have heq : q n = rowFormula k := by
    by_contra hne
    have hlt : q n < rowFormula k := by omega
    cases hk : k with
    | zero => simp [hk, rowFormula] at hlt; omega
    | succ j =>
      have hprev : ¬ q n ≤ rowFormula j := Nat.find_min hex (by omega : j < k)
      have hstep := upperCount_succ j
      by_cases hu : j + 1 < q (j + 1)
      · rw [if_pos hu] at hstep
        have hupper := q_eq_add_upperCount hu
        have hsame : q n = q (j + 1) := by
          simp only [hk, rowFormula] at hle hlt
          dsimp [rowFormula] at hprev
          omega
        have hcol := q_injective hsame
        omega
      · rw [if_neg hu] at hstep
        simp only [hk, rowFormula] at hle hlt
        dsimp [rowFormula] at hprev
        omega
  exact ⟨k, heq.symm⟩

/-- Infinitely many rows are occupied by lower queens. This justifies the sorted
enumeration introduced after Lemma 3 in Section 2. -/
theorem infinite_lowerRows (hsurj : Function.Surjective q) :
    Set.Infinite {r | IsLowerRow r} :=
  (Set.infinite_range_of_injective rowFormula_strictMono.injective).mono
    (by rintro r ⟨k, rfl⟩; exact rowFormula_lower hsurj k)

/-- **Lemma 4 (sorted lower rows).** With zero-based indexing,
`v(k) = k + 1 + U(k)`. The row permutation hypothesis is Lemma 3. -/
theorem sortedLowerRow_eq (hsurj : Function.Surjective q) (k : ℕ) :
    sortedLowerRow k = k + 1 + upperCount k := by
  have hinf := infinite_lowerRows hsurj
  have hindices (i : ℕ) : ∀ hf : Set.Finite (Set.ofPred IsLowerRow),
      i < hf.toFinset.card := fun hf => (hinf hf).elim
  have heq := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := IsLowerRow) rowFormula
    (fun r hr => by
      obtain ⟨i, hi⟩ := lowerRow_in_range_rowFormula hr
      exact ⟨i, hindices i, hi⟩)
    (fun i _ => rowFormula_lower hsurj i)
    (fun i _ j _ hij => rowFormula_strictMono hij)
  exact (heq (hindices k)).symm

/-- The sorted lower-row sequence is strictly increasing (Section 2). -/
theorem sortedLowerRow_strictMono (hsurj : Function.Surjective q) :
    StrictMono sortedLowerRow :=
  Nat.nth_strictMono (infinite_lowerRows hsurj)

/-- Sorting neither loses nor adds lower rows (Section 2). -/
theorem range_sortedLowerRow (hsurj : Function.Surjective q) :
    Set.range sortedLowerRow = {r | IsLowerRow r} :=
  Nat.range_nth_of_infinite (infinite_lowerRows hsurj)

/-- There are infinitely many lower columns, as asserted after Lemma 3 in Section 2.
Their image under `q` is the infinite set of lower rows. -/
theorem infinite_lowerColumns (hsurj : Function.Surjective q) :
    Set.Infinite {n | q n < n} := by
  intro hfinite
  apply infinite_lowerRows hsurj
  have himage := hfinite.image q
  convert himage using 1
  ext r
  simp [IsLowerRow, Set.mem_image]

end Queens
