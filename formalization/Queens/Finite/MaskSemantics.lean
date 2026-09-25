import Queens.Finite.Local
import Queens.LocalUpdates

/-!
# Semantics of offset bit masks

The records of Definition 10 are ordinary finite sets on the actual board and
bit masks in Algorithm 1. These kernel-checked identities justify insertion,
reference shifts, and the least-unused-diagonal search in the implementation.
-/

namespace Queens.Finite

/-- Section 4.2: the offset-membership test is the standard natural-number bit test. -/
theorem hasOffset_eq_testBit (mask offset : ℕ) :
    hasOffset mask offset = mask.testBit offset := by
  simp [hasOffset, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    Bool.beq_eq_decide_eq]

/-- Section 4.5: shifting a mask advances the reference by the shift amount. -/
theorem hasOffset_shiftRight (mask shift offset : ℕ) :
    hasOffset (mask >>> shift) offset = hasOffset mask (shift + offset) := by
  simp [hasOffset_eq_testBit, Nat.testBit_shiftRight]

/-- Section 4.5: mask insertion adds exactly the requested offset. -/
theorem hasOffset_insertOffset (mask added offset : ℕ) :
    hasOffset (insertOffset mask added) offset =
      (hasOffset mask offset || decide (added = offset)) := by
  simp [hasOffset_eq_testBit, insertOffset, Nat.shiftLeft_eq, Nat.testBit_two_pow]

/-- Section 4.5: mask insertion is precisely finite-set insertion. -/
@[simp] theorem offsets_insertOffset (mask added : ℕ) :
    offsets (insertOffset mask added) = insert added (offsets mask) := by
  ext offset
  simp only [mem_offsets, hasOffset_insertOffset, Finset.mem_insert,
    Bool.or_eq_true_iff, decide_eq_true_eq]
  exact or_comm.trans (or_congr eq_comm Iff.rfl)

/-- Equation (update), Section 4.5: right shift implements truncation followed
by subtraction of the new reference. -/
theorem offsets_shiftRight (mask shift : ℕ) :
    offsets (mask >>> shift) = retainedOffsets shift (offsets mask) := by
  ext offset
  rw [mem_offsets, hasOffset_shiftRight, mem_retainedOffsets]
  constructor
  · intro h
    exact ⟨shift + offset, mem_offsets.mpr h, by omega, by omega⟩
  · rintro ⟨v, hv, hshift, heq⟩
    have hveq : v = shift + offset := by omega
    simpa only [← hveq] using mem_offsets.mp hv

/-- Section 4.5: the mask-based diagonal search returns the least absent
nonnegative offset; its fallback is therefore unreachable. -/
theorem diagonalAdvance_spec (mask : ℕ) :
    diagonalAdvance mask ∉ offsets mask ∧
      ∀ offset < diagonalAdvance mask, offset ∈ offsets mask := by
  have hlast : hasOffset mask mask = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hm := (Finset.mem_filter.mp (mem_offsets.mpr h)).1
    have := Finset.mem_range.mp hm
    omega
  unfold diagonalAdvance
  cases hf : (List.range (mask + 1)).find? (fun h => !hasOffset mask h) with
  | none =>
      have hnone := List.find?_eq_none.mp hf mask (List.mem_range.mpr (by omega))
      simp [hlast] at hnone
  | some first =>
      obtain ⟨hfirst, i, hi, heq, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hf
      simp only [List.length_range, List.getElem_range] at hi heq hbefore
      subst first
      simp only [Option.getD_some]
      constructor
      · simpa only [mem_offsets, Bool.not_eq_true, Bool.not_eq_true'] using hfirst
      · intro offset hoffset
        have h := hbefore offset hoffset
        simpa only [Bool.not_not, mem_offsets] using h

/-- Section 4.5: the executable diagonal advance agrees with the mathematical
least-unused position of its decoded record. -/
theorem diagonalAdvance_eq_leastUnused (mask : ℕ) :
    diagonalAdvance mask = leastUnused (offsets mask) := by
  have hs := diagonalAdvance_spec mask
  apply Nat.le_antisymm
  · by_contra h
    exact leastUnused_not_mem _ (hs.2 _ (by omega))
  · exact leastUnused_le_of_not_mem hs.1

end Queens.Finite
