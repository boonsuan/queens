import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.ByContra

/-!
# Sorting preserves a uniform discrepancy bound

This is the order-theoretic argument in Lemma 6 of *Greedy Queens and the Golden Ratio*.
It is independent of the queen construction. A monotone reference sequence approximating
an enumeration also approximates any monotone rearrangement of that enumeration.

We index sequences from zero here. Translating the paper's positive indices by one does
not change the statement. An explicit permutation records the relationship between the
chronological enumeration and the sorted enumeration; no existence of a sorting is assumed
implicitly.
-/

namespace Queens

/-- An injection of natural numbers sends some element of the first `n + 1` indices to
an index at least `n`. This is the finite pigeonhole argument used in Lemma 6. -/
theorem exists_le_map_ge {f : ℕ → ℕ} (hf : Function.Injective f) (n : ℕ) :
    ∃ i ≤ n, n ≤ f i := by
  by_contra! h
  have hsubset : (Finset.range (n + 1)).image f ⊆ Finset.range n := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (h i (by have := Finset.mem_range.mp hi; omega))
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ hf, Finset.card_range, Finset.card_range] at hcard
  omega

/-- A permutation has an index at least `n` whose image is at most `n`.
This is the reverse pigeonhole argument in Lemma 6. -/
theorem exists_ge_perm_le (e : Equiv.Perm ℕ) (n : ℕ) :
    ∃ i ≥ n, e i ≤ n := by
  obtain ⟨j, hj, hn⟩ := exists_le_map_ge e.symm.injective n
  exact ⟨e.symm j, hn, by simpa using hj⟩

/-- **Lemma 6, sorting step**, in an ordered additive group. If the chronological sequence
`v ∘ e` stays within `C` of the monotone reference sequence `t`, the monotone enumeration
`v` satisfies the same bound. In the paper, `v` is the sequence of sorted lower rows and
`t j = xⱼᴸ - j`; `e` matches chronological rows with their sorted ranks. -/
theorem abs_sub_le_of_monotone_rearrangement
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {v t : ℕ → α} (hv : Monotone v) (ht : Monotone t)
    (e : Equiv.Perm ℕ) {C : α} (h : ∀ i, |v (e i) - t i| ≤ C) (n : ℕ) :
    |v n - t n| ≤ C := by
  rw [abs_sub_le_iff]
  constructor
  · obtain ⟨i, hin, hni⟩ := exists_le_map_ge e.injective n
    have hbound := sub_le_iff_le_add.mp (abs_sub_le_iff.mp (h i)).1
    apply sub_le_iff_le_add.mpr
    exact (hv hni).trans (hbound.trans (add_le_add le_rfl (ht hin)))
  · obtain ⟨i, hni, hin⟩ := exists_ge_perm_le e n
    have hbound := sub_le_iff_le_add.mp (abs_sub_le_iff.mp (h i)).2
    apply sub_le_iff_le_add.mpr
    exact (ht hni).trans (hbound.trans (add_le_add le_rfl (hv hin)))

end Queens
