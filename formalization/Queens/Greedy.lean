import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.SplitIfs

/-!
# Greedy queens: the defining rule and upper diagonals

This file defines the sequence from the introduction by choosing the least row
unattacked by earlier queens. It establishes the elementary nonattacking facts
and the upper-diagonal identity of Section 2, Lemma 2.
-/

namespace Queens

/-- A row is available in column `n` against the finite list of earlier queens.
The three inequalities exclude attacks along rows, diagonals, and antidiagonals.
This is the greedy placement rule in the introduction. -/
def Available (n r : ℕ) (previous : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, r ≠ previous i ∧ r + i.val ≠ previous i + n ∧
    r + n ≠ previous i + i.val

instance (n r : ℕ) (previous : Fin n → ℕ) : Decidable (Available n r previous) :=
  inferInstanceAs (Decidable (∀ i : Fin n, r ≠ previous i ∧
    r + i.val ≠ previous i + n ∧ r + n ≠ previous i + i.val))

/-- There is an available row: any row above the sum of the preceding rows
plus the column index is high enough. Thus the greedy rule is defined at every
column (introduction). -/
theorem exists_available (n : ℕ) (previous : Fin n → ℕ) :
    ∃ r, Available n r previous := by
  refine ⟨n + ∑ i, previous i + 1, ?_⟩
  intro i
  have hrow : previous i ≤ ∑ j, previous j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (previous j)) (Finset.mem_univ i)
  have hi := i.isLt
  constructor
  · omega
  constructor <;> omega

/-- The greedy queens sequence `q₀, q₁, …` of the introduction: choose the
least row not attacked by a queen in an earlier column. -/
noncomputable def q (n : ℕ) : ℕ :=
  Nat.find (exists_available n (fun i => q i.val))
termination_by n

/-- The queen chosen by the greedy rule is unattacked by all earlier queens. -/
theorem q_available (n : ℕ) : Available n (q n) (fun i => q i.val) := by
  conv => arg 2; rw [q]
  exact Nat.find_spec (exists_available n (fun i => q i.val))

/-- Every available row is at least the row chosen by the greedy rule. -/
theorem q_le_of_available {n r : ℕ}
    (hr : Available n r (fun i => q i.val)) : q n ≤ r := by
  rw [q]
  exact Nat.find_min' _ hr

/-- The three nonattacking conditions, stated for ordinary natural indices. -/
theorem q_safe {i n : ℕ} (hi : i < n) :
    q n ≠ q i ∧ q n + i ≠ q i + n ∧ q n + n ≠ q i + i :=
  q_available n ⟨i, hi⟩

/-- Distinct columns have distinct queen rows; the injectivity part of
Section 2, Lemma 3. -/
theorem q_injective : Function.Injective q := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact False.elim ((q_safe hlt).1 h.symm)
  · exact heq
  · exact False.elim ((q_safe hgt).1 h)

/-- The first queen occupies the origin (introduction). -/
@[simp] theorem q_zero : q 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply q_le_of_available
  intro i
  exact Fin.elim0 i

/-- The second queen is in row two (introduction). -/
@[simp] theorem q_one : q 1 = 2 := by
  have hle : q 1 ≤ 2 := by
    apply q_le_of_available
    intro i
    have hi : i.val = 0 := by omega
    simp
  have hs := q_safe (show 0 < 1 by omega)
  simp only [q_zero] at hs
  omega

/-- The queen at the origin excludes the main diagonal in every later
column, so every positive-column queen is upper or lower (Section 2). -/
theorem q_ne_self {n : ℕ} (hn : 0 < n) : q n ≠ n := by
  have hs := (q_safe hn).2.1
  simpa using hs

/-- Number of upper queens through column `n`, including column `n`.
This is `U(n)` in the counting equation of Section 2; the origin contributes zero. -/
noncomputable def upperCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun i => i < q i)).card

/-- There are no upper queens through column zero. -/
@[simp] theorem upperCount_zero : upperCount 0 = 0 := by
  simp [upperCount]

/-- Passing one column increases the upper count precisely when its queen
is above the main diagonal. -/
theorem upperCount_succ (n : ℕ) :
    upperCount (n + 1) = upperCount n + if n + 1 < q (n + 1) then 1 else 0 := by
  classical
  unfold upperCount
  rw [Finset.range_add_one (n := n + 1)]
  by_cases h : n + 1 < q (n + 1)
  · simp [Finset.filter_insert, h]
  · simp [Finset.filter_insert, h]

/-- Upper counts are monotone in the last column counted. -/
theorem upperCount_mono : Monotone upperCount := by
  intro m n hmn
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.range_mono (by omega))

/-- Every positive rank up to the upper count is attained by an upper
queen. This turns the count formulation of Lemma 2 into the paper's
`k`th-upper-queen formulation. -/
theorem upperCount_rank_exists {n k : ℕ} (hk : 0 < k)
    (hkn : k ≤ upperCount n) :
    ∃ i ≤ n, i < q i ∧ upperCount i = k := by
  induction n with
  | zero => simp at hkn; omega
  | succ n ih =>
    by_cases hprev : k ≤ upperCount n
    · obtain ⟨i, hin, hi, hcount⟩ := ih hprev
      exact ⟨i, by omega, hi, hcount⟩
    · have hupper : n + 1 < q (n + 1) := by
        by_contra h
        rw [upperCount_succ, if_neg h, Nat.add_zero] at hkn
        exact hprev hkn
      have hcount := upperCount_succ n
      rw [if_pos hupper] at hcount
      exact ⟨n + 1, le_rfl, hupper, by omega⟩

/-- **Lemma 2 (upper queens).** An upper queen in column `n` lies on
upper diagonal `U(n)`: its row is `n + U(n)`. Equivalently, the `k`th
upper queen lies on the `k`th upper diagonal. -/
theorem q_eq_add_upperCount {n : ℕ} (hn : n < q n) :
    q n = n + upperCount n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hcount : upperCount (n + 1) = upperCount n + 1 := by
        rw [upperCount_succ, if_pos hn]
      have hle : q (n + 1) ≤ n + 1 + (upperCount n + 1) := by
        apply q_le_of_available
        intro i
        dsimp only
        have hi : i.val ≤ n := by omega
        by_cases hu : i.val < q i.val
        · have hrow := ih i.val i.isLt hu
          have hmono := upperCount_mono hi
          constructor
          · omega
          constructor <;> omega
        · have hrow : q i.val ≤ i.val := by omega
          constructor
          · omega
          constructor <;> omega
      have hge : n + 1 + (upperCount n + 1) ≤ q (n + 1) := by
        by_contra h
        have hkpos : 0 < q (n + 1) - (n + 1) := by omega
        have hkle : q (n + 1) - (n + 1) ≤ upperCount n := by omega
        obtain ⟨i, hin, hi, hki⟩ := upperCount_rank_exists hkpos hkle
        have hil : i < n + 1 := by omega
        have hrow := ih i hil hi
        have hdiag := (q_safe hil).2.1
        omega
      omega

/-- At most one upper queen is added in each positive column. -/
theorem upperCount_le (n : ℕ) : upperCount n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [upperCount_succ]
    split_ifs <;> omega

/-- Every positive prefix contains the upper queen in column one. -/
theorem upperCount_pos {n : ℕ} (hn : 0 < n) : 0 < upperCount n := by
  have hone : upperCount 1 = 1 := by
    rw [show 1 = 0 + 1 from rfl, upperCount_succ]
    simp
  have hmono := upperCount_mono (show 1 ≤ n by omega)
  omega

/-- Distinct queens occupy distinct signed diagonals, as required for the
lower-diagonal sequence of Section 2. -/
theorem q_diagonal_injective : Function.Injective (fun n => (q n : ℤ) - (n : ℤ)) := by
  intro m n h
  change (q m : ℤ) - (m : ℤ) = (q n : ℤ) - (n : ℤ) at h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have hs := (q_safe hlt).2.1
    omega
  · exact heq
  · have hs := (q_safe hgt).2.1
    omega

/-- Distinct queens occupy distinct antidiagonals. -/
theorem q_antidiagonal_injective : Function.Injective (fun n => q n + n) := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact False.elim ((q_safe hlt).2.2 h.symm)
  · exact heq
  · exact False.elim ((q_safe hgt).2.2 h)

/-- An upper queen has a larger upper rank than every earlier column. -/
theorem upperCount_lt_of_upper {m n : ℕ} (hmn : m < n) (hn : n < q n) :
    upperCount m < upperCount n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hmono := upperCount_mono (show m ≤ k by omega)
  rw [upperCount_succ, if_pos hn]
  omega

/-- Successive upper rows differ by at least two, the observation following
Section 2, Lemma 2. -/
theorem upper_rows_gap {m n : ℕ} (hm : m < q m) (hn : n < q n) (hmn : m < n) :
    q m + 2 ≤ q n := by
  have hcount := upperCount_lt_of_upper hmn hn
  rw [q_eq_add_upperCount hm, q_eq_add_upperCount hn]
  omega

end Queens
