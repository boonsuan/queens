import Queens.Greedy
import Mathlib.Tactic.Ring

/-!
# Geometry behind the stored upper-queen tests

These are the coordinate identities in Section 4.4 and the estimates in the proof
of Lemma 16 (Section 5). They concern the actual greedy board, independently of
the representation used by the finite calculation.

In the paper, `m` is the least unused row, `κ = U(m - 1)`, and an upper queen in
column `i = m + h` has relative count `Γ(h) = U(i) - κ`. We retain `i` and `m` as
natural coordinates and take their difference in `ℤ`, avoiding truncated subtraction.
-/

namespace Queens

/-- The signed upper-count difference `Γ` from Section 4.4, evaluated at an
absolute column `i` relative to the reference row `m`. -/
noncomputable def relativeUpperCount (m i : ℕ) : ℤ :=
  (upperCount i : ℤ) - (upperCount (m - 1) : ℤ)

/-- The relative-row identity in equation (source-offsets), Section 4.4. -/
theorem upper_row_relative {i : ℕ} (hi : i < q i) (m : ℕ) :
    (q i : ℤ) - m - (upperCount (m - 1) : ℤ) =
      ((i : ℤ) - m) + relativeUpperCount m i := by
  rw [q_eq_add_upperCount hi]
  simp only [Nat.cast_add, relativeUpperCount]
  ring

/-- The relative-antidiagonal identity in equation (source-offsets), Section 4.4. -/
theorem upper_antidiagonal_relative {i : ℕ} (hi : i < q i) (m : ℕ) :
    (i : ℤ) + q i - 2 * m - (upperCount (m - 1) : ℤ) =
      2 * ((i : ℤ) - m) + relativeUpperCount m i := by
  rw [q_eq_add_upperCount hi]
  simp only [Nat.cast_add, relativeUpperCount]
  ring

/-- The upper-antidiagonal test of **Proposition 12**, before restricting to
retained source columns. An upper queen attacks `(n, m + r)` exactly when
`2h + Γ(h) = z + r`. -/
theorem upper_antidiagonal_test {i : ℕ} (hi : i < q i) (m n r : ℕ) :
    i + q i = n + (m + r) ↔
      2 * ((i : ℤ) - m) + relativeUpperCount m i =
        ((n : ℤ) - m - (upperCount (m - 1) : ℤ)) + r := by
  have hsource := upper_antidiagonal_relative hi m
  omega

/-- Upper-count differences are nonpositive to the left of the row reference.
This is the observation about `Γ(h)` for negative offsets in Sections 4–5. -/
theorem relativeUpperCount_nonpos {m i : ℕ} (hi : i < m) :
    relativeUpperCount m i ≤ 0 := by
  have hcount := upperCount_mono (show i ≤ m - 1 by omega)
  dsimp [relativeUpperCount]
  omega

/-- An upper source at or after the row reference contributes its own upper
column, so `Γ(h) ≥ 1`; used to exclude sources beyond the queue in Lemma 16. -/
theorem relativeUpperCount_pos {m i : ℕ} (hm : 0 < m) (hmi : m ≤ i)
    (hi : i < q i) : 1 ≤ relativeUpperCount m i := by
  have hcount := upperCount_lt_of_upper (show m - 1 < i by omega) hi
  dsimp [relativeUpperCount]
  omega

/-- An upper source before the twelve-symbol input history is below both row
thresholds and cannot attack a lower candidate's antidiagonal. These are the
old-source exclusions in **Lemma 16**. -/
theorem old_upper_source_irrelevant {i m n r : ℕ}
    (hi : i < q i) (hold : i + 13 ≤ m)
    (hz : -4 ≤ (n : ℤ) - m - (upperCount (m - 1) : ℤ)) :
    (q i : ℤ) < (n : ℤ) - 1 ∧ i + q i < n + (m + r) := by
  have hgamma := relativeUpperCount_nonpos (show i < m by omega)
  have hrow := upper_row_relative hi m
  have hanti := upper_antidiagonal_relative hi m
  constructor <;> omega

/-- An upper source beyond a queue of length at least `z` lies above the row
threshold `n`. This justifies omitting future sources from Proposition 13's
row-count adjustment in the proof of Lemma 16. -/
theorem future_upper_row_above {i m n length : ℕ}
    (hi : i < q i) (hm : 0 < m) (hfuture : m + length ≤ i)
    (hlength : (n : ℤ) - m - (upperCount (m - 1) : ℤ) ≤ length) :
    n < q i := by
  have hgamma := relativeUpperCount_pos hm (by omega : m ≤ i) hi
  have hrow := upper_row_relative hi m
  omega

/-- The candidate extension length excludes every upper source after the
queue from its antidiagonal attack test, as proved in Lemma 16. -/
theorem future_upper_antidiagonal_above {i m n r length : ℕ}
    (hi : i < q i) (hm : 0 < m) (hfuture : m + length ≤ i)
    (hlength : ((n : ℤ) - m - (upperCount (m - 1) : ℤ) + r) / 2 < length) :
    n + (m + r) < i + q i := by
  have hgamma := relativeUpperCount_pos hm (by omega : m ≤ i) hi
  have hanti := upper_antidiagonal_relative hi m
  omega

/-- No two consecutive rows are upper rows, the observation after Lemma 2
used to terminate the row search in Lemma 16. -/
theorem not_consecutive_upper_rows (r : ℕ) :
    ¬ ((∃ i, i < q i ∧ q i = r) ∧ (∃ j, j < q j ∧ q j = r + 1)) := by
  rintro ⟨⟨i, hi, hri⟩, ⟨j, hj, hrj⟩⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · have hgap := upper_rows_gap hi hj hij
    omega
  · subst j
    omega
  · have hgap := upper_rows_gap hj hi hij
    omega

/-- The candidate loop only requests offsets through four under Condition 15.
This is the candidate-request estimate in Lemma 16. -/
theorem candidate_request_le_four {w z r : ℤ}
    (hw : w ≤ 4) (hz : z ≤ 5) (hr : r ≤ w) :
    max r ((z + r) / 2) ≤ 4 := by
  omega

/-- The causality estimate in Lemma 16: with `κ ≥ 12` and `z ≥ -4`, every
request at most six places beyond `m` concerns a column already determined. -/
theorem request_before_current_column {m n κ : ℕ}
    (hκ : 12 ≤ κ) (hz : -4 ≤ (n : ℤ) - m - κ) : m + 6 < n := by
  omega

/-- The row search has an available offset by six: a lower-row record and the
newly chosen lower queen occupy offsets at most four, and at least one of rows
`m + 5`, `m + 6` is not upper. This is the existence argument for part (iii)
of Lemma 16. -/
theorem exists_free_offset_le_six (m r : ℕ) (R : Finset ℕ)
    (hR : ∀ a ∈ R, a ≤ 4) (hr : r ≤ 4) :
    ∃ μ ≤ 6, μ ∉ insert r R ∧ ¬ ∃ i, i < q i ∧ q i = m + μ := by
  have hfive : 5 ∉ insert r R := by simp only [Finset.mem_insert]; grind
  have hsix : 6 ∉ insert r R := by simp only [Finset.mem_insert]; grind
  by_cases hupper : ∃ i, i < q i ∧ q i = m + 5
  · refine ⟨6, le_rfl, hsix, ?_⟩
    intro hnext
    apply not_consecutive_upper_rows (m + 5)
    exact ⟨hupper, by simpa [Nat.add_assoc] using hnext⟩
  · exact ⟨5, by omega, hfive, hupper⟩

end Queens
