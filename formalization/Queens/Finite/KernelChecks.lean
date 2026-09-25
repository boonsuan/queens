import Mathlib.Data.List.Nodup

/-!
# Small, kernel-checked certificate combinators

The finite verifications of Sections 6.2–6.6 use these generic facts to avoid
quadratic duplicate searches and to assemble independently checked chunks.
They concern arbitrary finite data and make no assumption about the queens
construction or a certificate generator.
-/

namespace Queens.Finite

/-- Sections 6.2–6.3: distinct keys and recovery of each key from its payload
imply distinct payloads. This proves uniqueness without quadratic pair searches. -/
theorem nodup_values_of_nodup_keys {α β : Type} {entries : List (α × β)}
    {recover : β → Option α} (hkeys : (entries.map Prod.fst).Nodup)
    (hrecover : ∀ entry ∈ entries, recover entry.2 = some entry.1) :
    (entries.map Prod.snd).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hkeys ⊢
  apply List.Pairwise.imp_of_mem ?_ hkeys
  intro a b ha hb hab heq
  apply hab
  have h := (hrecover a ha).symm.trans ((congrArg recover heq).trans (hrecover b hb))
  exact Option.some.inj h

/-- Sections 6.2–6.6: a Boolean predicate holds on flattened chunks whenever
it holds on every chunk. This lets finite checks be split into bounded proofs. -/
theorem all_flatten_of_all_chunks {α : Type} {chunks : Array (List α)} {p : α → Bool}
    (h : ∀ i : Fin chunks.size, (chunks[i.val]).all p = true) :
    chunks.toList.flatten.toArray.all p = true := by
  rw [← Array.all_toList]
  simp only [List.all_flatten]
  apply List.all_eq_true.mpr
  intro chunk hchunk
  have hmem : chunk ∈ chunks := by simpa using hchunk
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hmem
  exact heq ▸ h ⟨i, hi⟩

end Queens.Finite
