import Queens.Finite.Local

/-!
# Kernel-efficient checking of history graphs

Definition 11 requires unique, bounded vertices and closure under every allowed
symbol. Strict subtree bounds establish uniqueness in one tree traversal. Each
edge destination is found by the checked lookup operation, avoiding quadratic
list-membership checks. These optimizations change only evaluation cost: the
result remains the original mathematical well-formedness predicate.
-/

namespace Queens.Finite

/-- Definition 11: a well-formed finite presentation has unique vertices,
valid base-four and edge-mask encodings, and contains every edge destination. -/
def HistoryGraph.WellFormed (graph : HistoryGraph) (memory : ℕ := historyLength) : Prop :=
  (graph.map Prod.fst).Nodup ∧ ∀ entry ∈ graph,
    entry.1 < 4 ^ memory ∧ entry.2 < 16 ∧
      ∀ symbol : Fin 4, hasOffset entry.2 symbol.val = true →
        destination entry.1 symbol.val memory ∈ graph.map Prod.fst

/-- Definition 11: the mathematical well-formedness predicate is decidable.
Large certificates use the verified sufficient check below for efficiency. -/
instance (graph : HistoryGraph) (memory : ℕ) : Decidable (graph.WellFormed memory) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Check strict binary-search ordering and bounded vertex encodings by passing
an inclusive lower bound and exclusive upper bound down the tree. -/
def checkHistoryBounds (lo hi : ℕ) : BinaryTree (ℕ × ℕ) → Bool
  | .nil => true
  | .node entry left right =>
      decide (lo ≤ entry.1 ∧ entry.1 < hi) &&
        checkHistoryBounds lo entry.1 left && checkHistoryBounds (entry.1 + 1) hi right

/-- Strict subtree bounds imply both uniqueness of vertex keys and the stated
bounds on every entry. This justifies the linear uniqueness check. -/
theorem checkHistoryBounds_sound {tree : BinaryTree (ℕ × ℕ)} {lo hi : ℕ}
    (h : checkHistoryBounds lo hi tree = true) :
    ((historyEntries tree).map Prod.fst).Nodup ∧
      ∀ entry ∈ historyEntries tree, lo ≤ entry.1 ∧ entry.1 < hi := by
  induction tree generalizing lo hi with
  | nil => simp [historyEntries, indexedEntries]
  | node entry left right ihl ihr =>
    simp only [checkHistoryBounds, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hbound, hl⟩, hr⟩ := h
    obtain ⟨hln, hlb⟩ := ihl hl
    obtain ⟨hrn, hrb⟩ := ihr hr
    constructor
    · simp only [historyEntries, indexedEntries, List.map_append, List.map_cons, List.nodup_append,
        List.nodup_cons]
      refine ⟨hln, ⟨?_, hrn⟩, ?_⟩
      · intro hmem
        obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
        have := (hrb a ha).1
        omega
      · intro a ha b hb
        obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
        have hal := (hlb ea hea).2
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · obtain ⟨eb, heb, rfl⟩ := List.mem_map.mp hb
          have hbl := (hrb eb heb).1
          omega
    · intro a ha
      simp only [historyEntries, indexedEntries, List.mem_append, List.mem_cons] at ha
      rcases ha with ha | rfl | ha
      · have hb := hlb a ha
        omega
      · exact hbound
      · have hb := hrb a ha
        omega

/-- Test a Boolean property at every history-tree entry without constructing
its in-order list. This is a traversal optimization for finite verification. -/
abbrev historyAll (p : ℕ × ℕ → Bool) : BinaryTree (ℕ × ℕ) → Bool := indexedAll p

/-- Tree traversal checks precisely the entries in the mathematical list view. -/
theorem historyAll_eq_true {p : ℕ × ℕ → Bool} {tree : BinaryTree (ℕ × ℕ)} :
    historyAll p tree = true ↔ ∀ entry ∈ historyEntries tree, p entry = true :=
  indexedAll_eq_true

/-- Check an entry's edge mask and find the destination of every allowed
four-symbol label. A failed lookup rejects the entry. -/
def checkHistoryEntry (graph : HistoryGraph) (memory : ℕ) (entry : ℕ × ℕ) : Bool :=
  decide (entry.2 < 16) && (List.range 4).all (fun symbol =>
    if hasOffset entry.2 symbol then
      (graph.lookup (destination entry.1 symbol memory)).isSome
    else true)

/-- A successful entry check gives the original edge-mask bound and closure
statement, using lookup soundness rather than trusting the search layout. -/
theorem checkHistoryEntry_sound {graph : HistoryGraph} {memory : ℕ} {entry : ℕ × ℕ}
    (h : checkHistoryEntry graph memory entry = true) :
    entry.2 < 16 ∧ ∀ symbol : Fin 4, hasOffset entry.2 symbol.val = true →
      destination entry.1 symbol.val memory ∈ graph.map Prod.fst := by
  obtain ⟨hmask, hedges⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true hmask, ?_⟩
  intro symbol hallowed
  have hedge := List.all_eq_true.mp hedges symbol.val (List.mem_range.mpr symbol.isLt)
  simp only [hallowed, if_true] at hedge
  cases hlookup : graph.lookup (destination entry.1 symbol.val memory) with
  | none => simp [hlookup] at hedge
  | some mask =>
    exact List.mem_map.mpr ⟨(_, mask), graph.lookup_mem hlookup, rfl⟩

/-- Definition 11: an efficient executable sufficient check for the full
well-formedness predicate, suitable for reduction by the Lean kernel. -/
def checkHistoryGraph (graph : HistoryGraph) (memory : ℕ := historyLength) : Bool :=
  checkHistoryBounds 0 (4 ^ memory) graph.tree &&
    historyAll (checkHistoryEntry graph memory) graph.tree

/-- The optimized tree checker establishes the original Definition 11,
including unique vertices and closure under every allowed output symbol. -/
theorem checkHistoryGraph_sound {graph : HistoryGraph} {memory : ℕ}
    (h : checkHistoryGraph graph memory = true) : graph.WellFormed memory := by
  obtain ⟨hbounds, hedges⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hnodup, hbound⟩ := checkHistoryBounds_sound hbounds
  refine ⟨hnodup, ?_⟩
  intro entry hentry
  exact ⟨(hbound entry hentry).2,
    checkHistoryEntry_sound (historyAll_eq_true.mp hedges entry hentry)⟩

/-- Definition 11: finding any mask proves that a vertex is listed. Finite
prefix checks use this efficient sufficient test instead of linear membership. -/
theorem HistoryGraph.mem_of_lookup_isSome {graph : HistoryGraph} {vertex : ℕ}
    (h : (graph.lookup vertex).isSome = true) : vertex ∈ graph.map Prod.fst := by
  cases hlookup : graph.lookup vertex with
  | none => simp [hlookup] at h
  | some mask => exact List.mem_map.mpr ⟨(_, mask), graph.lookup_mem hlookup, rfl⟩

end Queens.Finite
