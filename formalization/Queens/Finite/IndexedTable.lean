import Queens.Finite.IndexedTree
import Mathlib.Data.List.Basic

/-!
# Dense indices and list positions

The indexed certificates in Section 6 store a natural-number key beside each
payload. Checking that these keys enumerate a range identifies keys with list
positions. The payloads themselves need not be compared during this check.
-/

namespace Queens.Finite

/-- Section 6 certificate support: if the listed keys enumerate the natural
range in order, the key at position `i` is precisely `i`. -/
theorem indexed_key_eq_position {α : Type} {entries : List (ℕ × α)}
    (hkeys : entries.map Prod.fst = List.range entries.length)
    {i : ℕ} (hi : i < entries.length) : entries[i].1 = i := by
  have h := congrArg (fun l : List ℕ => l[i]?) hkeys
  rw [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    List.getElem?_range hi] at h
  exact Option.some.inj h

/-- Section 6 certificate support: dense ordered keys turn entry membership
into an exact indexed lookup, without comparing or computing the payloads. -/
theorem indexed_mem_iff_getElem? {α : Type} {entries : List (ℕ × α)}
    (hkeys : entries.map Prod.fst = List.range entries.length) {i : ℕ} {a : α} :
    (i, a) ∈ entries ↔ entries[i]? = some (i, a) := by
  constructor
  · intro hmem
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
    have hindex := indexed_key_eq_position hkeys hj
    rw [heq] at hindex
    change i = j at hindex
    subst i
    exact List.getElem?_eq_some_iff.mpr ⟨hj, heq⟩
  · exact List.mem_of_getElem?

/-- Section 6 certificate support: a listed entry's fields agree with the
corresponding position in any projected list. This transfers a fast tree lookup
to the public state and adjacency arrays. -/
theorem indexed_field_getElem? {α β : Type} {entries : List (ℕ × α)}
    (hkeys : entries.map Prod.fst = List.range entries.length)
    (field : α → β) {i : ℕ} {a : α} (hmem : (i, a) ∈ entries) :
    (entries.map (fun entry => field entry.2))[i]? = some (field a) := by
  rw [List.getElem?_map, (indexed_mem_iff_getElem? hkeys).mp hmem]
  rfl

end Queens.Finite
