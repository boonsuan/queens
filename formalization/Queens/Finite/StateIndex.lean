import Queens.Finite.Local
import Queens.Finite.IndexedTree

/-!
# Kernel-efficient state lookup

Proposition 17's state table is indexed in two ways by the same proposed binary
tree: by state value for successor membership, and by natural-number position
for auxiliary witnesses. Both lookups check equality before returning a result.
Their soundness therefore requires no assumption about ordering or balance.
-/

namespace Queens.Finite

/-- Section 6.3: in-order entries of a proposed indexed state table. -/
abbrev stateIndexEntries : BinaryTree (ℕ × State) → List (ℕ × State) := indexedEntries

/-- Proposition 17: find a state's proposed index, checking equality at the
returned node. A malformed search layout can only cause lookup failure. -/
def lookupState (s : State) : BinaryTree (ℕ × State) → Option ℕ
  | .nil => none
  | .node entry left right =>
      if s = entry.2 then some entry.1
      else if compare s entry.2 = .lt then lookupState s left else lookupState s right

/-- Proposition 17: lookup by natural-number index, with a checked equality
at the returned node. -/
abbrev lookupStateIndex (i : ℕ) : BinaryTree (ℕ × State) → Option State := indexedLookup i

/-- Every successful lookup by state identifies an actual indexed tree entry. -/
theorem lookupState_mem {tree : BinaryTree (ℕ × State)} {s : State} {i : ℕ}
    (h : lookupState s tree = some i) : (i, s) ∈ stateIndexEntries tree := by
  induction tree with
  | nil => simp [lookupState] at h
  | node entry left right ihl ihr =>
    by_cases heq : s = entry.2
    · have hi : entry.1 = i := by simpa [lookupState, heq] using h
      simp only [stateIndexEntries, indexedEntries, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inl (Prod.ext hi.symm heq))
    · by_cases hlt : compare s entry.2 = .lt
      · have hm := ihl (by simpa [lookupState, heq, hlt] using h)
        exact List.mem_append.mpr (Or.inl hm)
      · have hm := ihr (by simpa [lookupState, heq, hlt] using h)
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hm)))

/-- Every successful lookup by index identifies an actual indexed tree entry. -/
theorem lookupStateIndex_mem {tree : BinaryTree (ℕ × State)} {s : State} {i : ℕ}
    (h : lookupStateIndex i tree = some s) : (i, s) ∈ stateIndexEntries tree :=
  indexedLookup_mem h

/-- Sections 6.3–6.6: check a property of every indexed state directly on the
tree, without materializing a large flattened array during kernel reduction. -/
abbrev stateIndexAll (p : ℕ × State → Bool) : BinaryTree (ℕ × State) → Bool := indexedAll p

/-- Direct tree checks establish the predicate at every mathematical entry. -/
theorem stateIndexAll_eq_true {tree : BinaryTree (ℕ × State)} {p : ℕ × State → Bool} :
    stateIndexAll p tree = true ↔ ∀ entry ∈ stateIndexEntries tree, p entry = true :=
  indexedAll_eq_true

end Queens.Finite
