import Queens.Finite.IndexedTree

/-!
# Vertex payloads for the repeated-run certificate

Corollary 19 uses several fields at each numbered forty-symbol state. A single
balanced lookup shares their index and avoids large-array normalization during
kernel checking. The upper bit and adjacency are independently aligned with the
original state graph; the remaining lengths are checked certificate proposals.
-/

namespace Queens.Finite

/-- Corollary 19: local data at a numbered state used by the run-graph checker. -/
structure RunVertexData where
  /-- Whether the latest output column is upper. -/
  upper : Bool
  /-- Original state-graph successors, before path contraction. -/
  successors : List ℕ
  /-- Proposed remaining lengths of label-one paths before a different edge. -/
  ones : List ℕ
  /-- Proposed remaining lengths of label-two paths before a different edge. -/
  twos : List ℕ
  /-- Proposed remaining lengths of label-three paths before a different edge. -/
  threes : List ℕ
  deriving DecidableEq

end Queens.Finite
