import Queens.LocalBoard
import Queens.Word

/-!
# Transferring a checked prefix to the actual board

The starting boards in Section 6.1 and Corollary 19 use different finite row
certificates. Once a certificate agrees with `q` on its prefix, the same local
identities identify its occupied rows, lower diagonals, records, and queen word.
This file contains those identities independently of either numerical table.
-/

namespace Queens

/-- Section 6.1 and Corollary 19: a proposed least unused value is characterized
by being absent while every smaller value is present. -/
theorem leastUnused_eq_of_spec {s : Finset ℕ} {m : ℕ}
    (hm : m ∉ s) (hsmaller : ∀ r < m, r ∈ s) : leastUnused s = m := by
  apply Nat.le_antisymm (leastUnused_le_of_not_mem hm)
  by_contra h
  exact leastUnused_not_mem s (hsmaller (leastUnused s) (by omega))

/-- Definition 9 on a checked prefix: the symbol in column `n` depends only on
its row and the rows in earlier columns. Used for both starting-board checks. -/
theorem queenSymbol_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i ≤ n, q i = rows i) :
    queenSymbol n = 2 * (if n < rows n then 1 else 0) +
      if ∃ i : Fin n, i.val < rows i.val ∧ rows i.val = n then 1 else 0 := by
  have heq : (∃ i : Fin n, i.val < q i.val ∧ q i.val = n) ↔
      ∃ i : Fin n, i.val < rows i.val ∧ rows i.val = n := by
    apply exists_congr
    intro i
    rw [hrows i.val i.isLt.le]
  simp only [queenSymbol, columnBit, upperRowBit, hrows n le_rfl, heq]

/-- Section 6.1 and Corollary 19: occupied rows are computed from any row
function agreeing with the actual queens strictly before the current column. -/
theorem occupiedRows_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i < n, q i = rows i) :
    occupiedRows n = (Finset.range n).image rows :=
  Finset.image_congr fun i hi => hrows i (Finset.mem_range.mp hi)

/-- Section 6.1 and Corollary 19: the lower-column set can be read from a
checked prefix, independently of how its row certificate was verified. -/
theorem earlierLowerColumns_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i < n, q i = rows i) :
    earlierLowerColumns n = (Finset.range n).filter (fun i => rows i < i) := by
  apply Finset.filter_congr
  intro i hi
  rw [hrows i (Finset.mem_range.mp hi)]

private theorem filter_image_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i < n, q i = rows i) (keep : ℕ → ℕ → Prop)
    [∀ i, DecidablePred (keep i)] (value : ℕ → ℕ → ℕ) :
    ((Finset.range n).filter (fun i => keep i (q i))).image (fun i => value i (q i)) =
      ((Finset.range n).filter (fun i => keep i (rows i))).image
        (fun i => value i (rows i)) := by
  have hfilter : (Finset.range n).filter (fun i => keep i (q i)) =
      (Finset.range n).filter (fun i => keep i (rows i)) := by
    apply Finset.filter_congr
    intro i hi
    rw [hrows i (Finset.mem_range.mp hi)]
  rw [hfilter]
  apply Finset.image_congr
  intro i hi
  exact congrArg (value i) (hrows i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))

/-- Section 6.1 and Corollary 19: occupied lower diagonals are exactly the
positive differences read from the lower queens of a checked prefix. -/
theorem lowerDiagonals_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i < n, q i = rows i) :
    lowerDiagonals n =
      ((Finset.range n).filter (fun i => rows i < i)).image (fun i => i - rows i) :=
  filter_image_eq_of_prefix hrows (fun i r => r < i) (fun i r => i - r)

/-- Definition 10 in the starting-board checks: the row-offset record is
computed from the checked prefix and the actual row reference. -/
theorem rowOffsets_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i < n, q i = rows i) :
    rowOffsets n =
      ((Finset.range n).filter (fun i => rows i < i ∧ rowReference n ≤ rows i)).image
        (fun i => rows i - rowReference n) := by
  simpa only [rowOffsets, earlierLowerColumns, Finset.filter_filter] using
    filter_image_eq_of_prefix hrows (fun i r => r < i ∧ rowReference n ≤ r)
      (fun _ r => r - rowReference n)

/-- Definition 10 in the starting-board checks: the antidiagonal-offset record
is computed from the checked prefix and the actual row reference. -/
theorem antidiagonalOffsets_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i < n, q i = rows i) :
    antidiagonalOffsets n =
      ((Finset.range n).filter (fun i => rows i < i ∧ n + rowReference n ≤ i + rows i)).image
        (fun i => i + rows i - (n + rowReference n)) := by
  simpa only [antidiagonalOffsets, earlierLowerColumns, Finset.filter_filter] using
    filter_image_eq_of_prefix hrows (fun i r => r < i ∧ n + rowReference n ≤ i + r)
      (fun i r => i + r - (n + rowReference n))

/-- Section 6.1 and Corollary 19: the upper count through a column is computed
from any prefix containing that column. -/
theorem upperCount_eq_of_prefix {rows : ℕ → ℕ} {n : ℕ}
    (hrows : ∀ i ≤ n, q i = rows i) :
    upperCount n = ((Finset.range (n + 1)).filter (fun i => i < rows i)).card := by
  unfold upperCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [hrows i (by have := Finset.mem_range.mp hi; omega)]

end Queens
