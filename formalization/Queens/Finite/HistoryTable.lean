import Queens.Finite.IndexedTree

/-!
# Kernel-efficient history tables

Definition 11's finite graph is stored as a binary tree so that individual
lookups reduce along a short branch in the Lean kernel. The supplied data
use balanced trees. Correctness does not assume balance or ordering: a
successful lookup is proved to return a listed entry, and an unsuccessful
request rejects the entire calculation. Graph closure is checked separately.
-/

namespace Queens.Finite

/-- Definition 11: the finite vertex-mask table, stored in a binary tree.
The tree shape affects evaluation cost but is not a trusted invariant. -/
structure HistoryGraph where
  /-- The untrusted binary search layout of the vertex-mask pairs. -/
  tree : BinaryTree (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- In-order traversal supplies the mathematical list of history entries.
This view is used for graph closure and finite cardinality assertions. -/
abbrev historyEntries : BinaryTree (ℕ × ℕ) → List (ℕ × ℕ) := indexedEntries

/-- Definition 11: the entries of the finite history graph. -/
def HistoryGraph.entries (graph : HistoryGraph) : List (ℕ × ℕ) :=
  historyEntries graph.tree

/-- Membership in a history graph means membership in its entry list. -/
instance : Membership (ℕ × ℕ) HistoryGraph where
  mem graph entry := entry ∈ graph.entries

/-- A universal property of the finite history entries is decidable. -/
instance (graph : HistoryGraph) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    Decidable (∀ entry ∈ graph, P entry) :=
  inferInstanceAs (Decidable (∀ entry ∈ graph.entries, P entry))

/-- Map the entry list, for the vertex and edge counts in Proposition 17. -/
def HistoryGraph.map {α : Type*} (graph : HistoryGraph) (f : ℕ × ℕ → α) : List α :=
  graph.entries.map f

/-- Number of listed history vertices, as in Proposition 17. -/
def HistoryGraph.length (graph : HistoryGraph) : ℕ := graph.entries.length

/-- Search a proposed binary layout. Equality is checked before returning a
mask, so malformed layouts cannot fabricate a vertex-mask pair. -/
abbrev historyLookup (vertex : ℕ) : BinaryTree (ℕ × ℕ) → Option ℕ :=
  indexedLookup vertex

/-- Definition 11: find the allowed-symbol mask, failing when the proposed
search layout does not supply that vertex. -/
def HistoryGraph.lookup (graph : HistoryGraph) (vertex : ℕ) : Option ℕ :=
  historyLookup vertex graph.tree

/-- A successful lookup returns an actual entry, for every proposed tree.
This is the soundness fact used when extending the actual word's graph path. -/
theorem historyLookup_mem {tree : BinaryTree (ℕ × ℕ)} {vertex mask : ℕ}
    (hlookup : historyLookup vertex tree = some mask) :
    (vertex, mask) ∈ historyEntries tree :=
  indexedLookup_mem hlookup

/-- Every successful history lookup comes from a listed vertex-mask pair,
independently of balance or ordering of the generated tree. -/
theorem HistoryGraph.lookup_mem {graph : HistoryGraph} {vertex mask : ℕ}
    (hlookup : graph.lookup vertex = some mask) : (vertex, mask) ∈ graph :=
  historyLookup_mem hlookup

end Queens.Finite
