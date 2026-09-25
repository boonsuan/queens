import Queens.Greedy
import Mathlib.Data.Nat.Nth

/-!
# Lower columns and their ranks

The lower-column enumeration is chronological and zero-indexed: `lowerColumn k`
is the paper's `xᴸₖ₊₁`. The counting identities and endpoint inequalities here
provide the combinatorial inputs to Section 3, Lemma 7. Results about all ranks
take infinitude of the lower columns as an explicit hypothesis.
-/

namespace Queens

/-- The lower queen's column at zero-based chronological rank `k`.
Thus this is `xᴸₖ₊₁` in Sections 2 and 3. -/
noncomputable def lowerColumn (k : ℕ) : ℕ :=
  Nat.nth (fun n => q n < n) k

/-- Number of lower queens through column `n`, written as the complementary
count `L(n) = n - U(n)` from Section 3. The origin counts as neither type. -/
noncomputable def lowerCount (n : ℕ) : ℕ := n - upperCount n

/-- The chronological lower-column enumeration is strictly increasing. -/
theorem lowerColumn_strictMono (hInfinite : Set.Infinite {n | q n < n}) :
    StrictMono lowerColumn := Nat.nth_strictMono hInfinite

/-- Every term of the lower-column enumeration contains a lower queen. -/
theorem lowerColumn_lower (hInfinite : Set.Infinite {n | q n < n}) (k : ℕ) :
    q (lowerColumn k) < lowerColumn k := Nat.nth_mem_of_infinite hInfinite k

/-- Every lower queen appears in the chronological lower-column enumeration. -/
theorem exists_lowerColumn_eq {n : ℕ} (hn : q n < n) :
    ∃ k, lowerColumn k = n := Nat.subset_range_nth hn

/-- The complementary count really counts lower queens. The offset by one
comes from `Nat.count` excluding its upper endpoint. -/
theorem count_lower_eq_lowerCount (n : ℕ) :
    Nat.count (fun i => q i < i) (n + 1) = lowerCount n := by
  unfold lowerCount
  induction n with
  | zero => simp [Nat.count_one]
  | succ n ih =>
    rw [Nat.count_succ, ih, upperCount_succ]
    have hbound := upperCount_le n
    by_cases hlower : q (n + 1) < n + 1
    · have hupper : ¬n + 1 < q (n + 1) := by omega
      simp only [if_pos hlower, if_neg hupper]
      omega
    · have hupper : n + 1 < q (n + 1) := by
        have hne := q_ne_self (show 0 < n + 1 by omega)
        omega
      simp only [if_neg hlower, if_pos hupper]
      omega

/-- At the `k`th zero-based lower column, exactly `k + 1` lower queens
have appeared. This is the rank identity used in Section 3. -/
theorem lowerCount_lowerColumn (hInfinite : Set.Infinite {n | q n < n}) (k : ℕ) :
    lowerCount (lowerColumn k) = k + 1 := by
  rw [← count_lower_eq_lowerCount]
  exact Nat.count_nth_succ_of_infinite hInfinite k

/-- Section 3's rank identity: the column is the number of upper queens
plus the positive rank of its lower queen. The origin contributes neither count. -/
theorem lowerColumn_eq_upperCount_add_rank
    (hInfinite : Set.Infinite {n | q n < n}) (k : ℕ) :
    lowerColumn k = upperCount (lowerColumn k) + k + 1 := by
  have hrank := lowerCount_lowerColumn hInfinite k
  have hbound := upperCount_le (lowerColumn k)
  unfold lowerCount at hrank
  omega

/-- The upper count at a lower column is the column minus its positive rank:
`U(xᴸⱼ) = xᴸⱼ - j`, as used in equation (rank-row) of Section 3. -/
theorem upperCount_lowerColumn (hInfinite : Set.Infinite {n | q n < n}) (k : ℕ) :
    upperCount (lowerColumn k) = lowerColumn k - (k + 1) := by
  have hrank := lowerColumn_eq_upperCount_add_rank hInfinite k
  omega

/-- The comparison sequence `tₖ = U(xᴸₖ₊₁)` is monotone, the order hypothesis
needed by the sorting argument in Section 3, Lemma 6. -/
theorem lowerColumn_upperCount_mono (hInfinite : Set.Infinite {n | q n < n}) :
    Monotone (fun k => upperCount (lowerColumn k)) :=
  upperCount_mono.comp (lowerColumn_strictMono hInfinite).monotone

/-- The rank-row identity from Section 3: the error of a lower row from the
upper count is the negative of its diagonal-magnitude error from its rank. -/
theorem lower_row_count_identity (hInfinite : Set.Infinite {n | q n < n}) (k : ℕ) :
    (q (lowerColumn k) : ℤ) - (upperCount (lowerColumn k) : ℤ) =
      ((k : ℤ) + 1) - ((lowerColumn k : ℤ) - (q (lowerColumn k) : ℤ)) := by
  have hrank := lowerColumn_eq_upperCount_add_rank hInfinite k
  omega

/-- Diagonal discrepancy and chronological lower-row discrepancy are the
same absolute error, by the rank-row identity in Section 3. -/
theorem lower_row_count_discrepancy (hInfinite : Set.Infinite {n | q n < n})
    (k : ℕ) (C : ℤ)
    (hdiag : |(lowerColumn k : ℤ) - (q (lowerColumn k) : ℤ) - ((k : ℤ) + 1)| ≤ C) :
    |(q (lowerColumn k) : ℤ) - (upperCount (lowerColumn k) : ℤ)| ≤ C := by
  rw [lower_row_count_identity hInfinite k, abs_sub_comm]
  exact hdiag

/-- If at least one lower queen has appeared, its last lower column is at
most the current column. This is the left endpoint used in Lemma 7. -/
theorem lowerColumn_left (n : ℕ) (hpositive : 0 < lowerCount n) :
    lowerColumn (lowerCount n - 1) ≤ n := by
  have hlt : lowerCount n - 1 < Nat.count (fun i => q i < i) (n + 1) := by
    rw [count_lower_eq_lowerCount]
    omega
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hlt)

/-- The next lower column lies strictly after the current column. This is
the right endpoint used in Section 3, Lemma 7, also when the lower count is zero. -/
theorem lowerColumn_right (hInfinite : Set.Infinite {n | q n < n}) (n : ℕ) :
    n < lowerColumn (lowerCount n) := by
  have h := Nat.le_nth_count hInfinite (n + 1)
  rw [count_lower_eq_lowerCount] at h
  exact h

end Queens
