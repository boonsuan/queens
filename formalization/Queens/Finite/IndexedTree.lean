import Mathlib.Data.Tree.Basic

/-!
# Checked natural-number lookup in finite trees

The finite certificates in Section 6 use balanced layouts for efficient kernel
reduction. These generic operations never assume the supplied layout is sorted:
a successful lookup is proved to identify an actual entry. Ordering is needed
only to make all requested lookups succeed, which the certificate checks.
-/

namespace Queens.Finite

/-- Section 6 certificate support: the mathematical in-order view of a tree. -/
def indexedEntries {α : Type} : BinaryTree (ℕ × α) → List (ℕ × α)
  | .nil => []
  | .node entry left right => indexedEntries left ++ entry :: indexedEntries right

/-- Section 6 certificate support: lookup checks equality before returning a
value; an unsuitable search layout produces failure rather than a false match. -/
def indexedLookup {α : Type} (i : ℕ) : BinaryTree (ℕ × α) → Option α
  | .nil => none
  | .node entry left right =>
      if i = entry.1 then some entry.2
      else if i < entry.1 then indexedLookup i left else indexedLookup i right

/-- Every successful natural-number lookup identifies a listed entry. -/
theorem indexedLookup_mem {α : Type} {tree : BinaryTree (ℕ × α)} {a : α} {i : ℕ}
    (h : indexedLookup i tree = some a) : (i, a) ∈ indexedEntries tree := by
  induction tree with
  | nil => simp [indexedLookup] at h
  | node entry left right ihl ihr =>
    by_cases heq : i = entry.1
    · have ha : entry.2 = a := by simpa [indexedLookup, heq] using h
      simp only [indexedEntries, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inl (Prod.ext heq ha.symm))
    · by_cases hlt : i < entry.1
      · have hm := ihl (by simpa [indexedLookup, heq, hlt] using h)
        exact List.mem_append.mpr (Or.inl hm)
      · have hm := ihr (by simpa [indexedLookup, heq, hlt] using h)
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hm)))

/-- Section 6 certificate support: test each entry without constructing its
flattened list, so reductions follow the bounded-depth tree directly. -/
def indexedAll {α : Type} (p : ℕ × α → Bool) : BinaryTree (ℕ × α) → Bool
  | .nil => true
  | .node entry left right => p entry && indexedAll p left && indexedAll p right

/-- Direct traversal verifies the predicate at every mathematical entry. -/
theorem indexedAll_eq_true {α : Type} {tree : BinaryTree (ℕ × α)} {p : ℕ × α → Bool} :
    indexedAll p tree = true ↔ ∀ entry ∈ indexedEntries tree, p entry = true := by
  induction tree with
  | nil => simp [indexedAll, indexedEntries]
  | node entry left right ihl ihr =>
    simp only [indexedAll, Bool.and_eq_true, ihl, ihr, indexedEntries,
      List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨⟨he, hl⟩, hr⟩ entry (h | rfl | h)
      · exact hl entry h
      · exact he
      · exact hr entry h
    · intro h
      exact ⟨⟨h entry (Or.inr (Or.inl rfl)), fun entry he => h entry (Or.inl he)⟩,
        fun entry he => h entry (Or.inr (Or.inr he))⟩

/-- A linear comparison with an indexed list, together with successful
self-lookups at tree entries, identifies every requested list position. This
avoids rechecking a large array separately at every index during kernel evaluation. -/
theorem indexedLookup_of_list_alignment {α β : Type} {tree : BinaryTree (ℕ × α)}
    {values : List β} {field : α → β}
    (hself : ∀ entry ∈ indexedEntries tree, indexedLookup entry.1 tree = some entry.2)
    (halign : (indexedEntries tree).map (fun entry => (entry.1, field entry.2)) =
      values.zipIdx.map Prod.swap) {i : ℕ} (hi : i < values.length) :
    ∃ a, indexedLookup i tree = some a ∧ field a = values[i] := by
  have hz : (values[i], i) ∈ values.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  have hm : (i, values[i]) ∈ (indexedEntries tree).map (fun entry => (entry.1, field entry.2)) := by
    rw [halign]
    exact List.mem_map.mpr ⟨(values[i], i), hz, rfl⟩
  obtain ⟨⟨j, a⟩, ha, heq⟩ := List.mem_map.mp hm
  have hji : j = i := congrArg Prod.fst heq
  have hfield : field a = values[i] := congrArg Prod.snd heq
  subst j
  exact ⟨a, hself (i, a) ha, hfield⟩

/-- A successful lookup has the field stored at its list index whenever the
in-order field list agrees with the indexed mathematical list. This direction
does not require a separate self-lookup check. -/
theorem indexedLookup_field_eq_getElem? {α β : Type} {tree : BinaryTree (ℕ × α)}
    {values : List β} {field : α → β}
    (halign : (indexedEntries tree).map (fun entry => (entry.1, field entry.2)) =
      values.zipIdx.map Prod.swap) {i : ℕ} {a : α}
    (hlookup : indexedLookup i tree = some a) : values[i]? = some (field a) := by
  have hm := indexedLookup_mem hlookup
  have hf : (i, field a) ∈ values.zipIdx.map Prod.swap := by
    rw [← halign]
    exact List.mem_map.mpr ⟨(i, a), hm, rfl⟩
  obtain ⟨⟨value, j⟩, hj, heq⟩ := List.mem_map.mp hf
  have hji : j = i := congrArg Prod.fst heq
  have hva : value = field a := congrArg Prod.snd heq
  subst j
  subst value
  exact List.mk_mem_zipIdx_iff_getElem?.mp hj

end Queens.Finite
