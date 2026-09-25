import Queens.LabeledRuns

/-!
# Bounded contraction of column paths

The run graph in Appendix A contracts a block of upper columns followed by a
nonempty block of lower columns and its next upper endpoint. The bounds already
proved in Corollary 19 permit exhaustive, bounded searches. These lemmas prove
that every actual path of the prescribed form is retained by those searches.
-/

namespace Queens.Finite

/-- Appendix A: a directed graph represented by finite successor lists. -/
abbrev Adjacency := ℕ → List ℕ

/-- Appendix A: an infinite path in a finite adjacency presentation. -/
def Adjacency.IsPath (graph : Adjacency) (vertices : ℕ → ℕ) : Prop :=
  ∀ n, vertices (n + 1) ∈ graph (vertices n)

/-- Appendix A: follow edges until first reaching a vertex satisfying `stop`,
retaining its vertex and the number of edges. The search explores every branch
up to `fuel`; exhaustion contributes no path. -/
def firstHits (graph : Adjacency) (stop : ℕ → Bool) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | fuel + 1, v => (graph v).flatMap fun w =>
      if stop w then [(w, 1)] else
        (firstHits graph stop fuel w).map fun p => (p.1, p.2 + 1)

/-- Appendix A: bounded first-hit search retains every path whose first
stopping vertex is reached within the supplied fuel. -/
theorem firstHits_mem {graph : Adjacency} {stop : ℕ → Bool}
    {vertices : ℕ → ℕ} (hpath : graph.IsPath vertices) {fuel start length : ℕ}
    (hpos : 0 < length) (hlen : length ≤ fuel)
    (hend : stop (vertices (start + length)) = true)
    (hinterior : ∀ i : Fin length, 0 < i.val → stop (vertices (start + i.val)) = false) :
    (vertices (start + length), length) ∈ firstHits graph stop fuel (vertices start) := by
  induction fuel generalizing start length with
  | zero => omega
  | succ fuel ih =>
    rw [firstHits]
    apply List.mem_flatMap.mpr
    refine ⟨vertices (start + 1), hpath start, ?_⟩
    by_cases hl : length = 1
    · subst length
      simp [hend]
    · have hnext : stop (vertices (start + 1)) = false := by
        exact hinterior ⟨1, by omega⟩ Nat.zero_lt_one
      rw [hnext]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map]
      have hnpos : 0 < length - 1 := by omega
      have hnlen : length - 1 ≤ fuel := by omega
      have heq : start + 1 + (length - 1) = start + length := by omega
      have hend' : stop (vertices (start + 1 + (length - 1))) = true := by
        simpa only [heq] using hend
      have hinterior' : ∀ i : Fin (length - 1), 0 < i.val →
          stop (vertices (start + 1 + i.val)) = false := by
        intro i hi
        have hi' := i.isLt
        have h := hinterior ⟨i.val + 1, by omega⟩ (by dsimp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      refine ⟨(vertices (start + 1 + (length - 1)), length - 1),
        ih hnpos hnlen hend' hinterior', ?_⟩
      simp only [heq]
      congr 1
      omega

/-- Appendix A: skip at most `fuel - 1` upper outputs, then follow the first
lower output to its next upper endpoint. The edge label counts lower columns. -/
def runTargets (graph : Adjacency) (upper : ℕ → Bool) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | fuel + 1, v => (graph v).flatMap fun w =>
      if upper w then runTargets graph upper fuel w else firstHits graph upper 3 w

/-- Appendix A: every bounded upper-then-lower block is retained by the
contracted run graph, labeled by its number of lower columns. -/
theorem runTargets_mem {graph : Adjacency} {upper : ℕ → Bool}
    {vertices : ℕ → ℕ} (hpath : graph.IsPath vertices) {fuel start distance length : ℕ}
    (hdpos : 0 < distance) (hdfuel : distance ≤ fuel)
    (hlpos : 0 < length) (hlen : length ≤ 3)
    (hu : ∀ i : Fin distance, 0 < i.val → upper (vertices (start + i.val)) = true)
    (hl : ∀ i : Fin length, upper (vertices (start + distance + i.val)) = false)
    (hend : upper (vertices (start + distance + length)) = true) :
    (vertices (start + distance + length), length) ∈
      runTargets graph upper fuel (vertices start) := by
  induction fuel generalizing start distance with
  | zero => omega
  | succ fuel ih =>
    rw [runTargets]
    apply List.mem_flatMap.mpr
    refine ⟨vertices (start + 1), hpath start, ?_⟩
    by_cases hd : distance = 1
    · subst distance
      have hfirst := hl ⟨0, hlpos⟩
      simp only [Nat.add_zero] at hfirst
      rw [hfirst]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply firstHits_mem hpath hlpos hlen hend
      intro i hi
      exact hl i
    · have hnext : upper (vertices (start + 1)) = true := hu ⟨1, by omega⟩ Nat.zero_lt_one
      rw [hnext]
      simp only [↓reduceIte]
      have heq : start + 1 + (distance - 1) = start + distance := by omega
      have hu' : ∀ i : Fin (distance - 1), 0 < i.val →
          upper (vertices (start + 1 + i.val)) = true := by
        intro i hi
        have hi' := i.isLt
        have h := hu ⟨i.val + 1, by omega⟩ (by dsimp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hl' : ∀ i : Fin length,
          upper (vertices (start + 1 + (distance - 1) + i.val)) = false := by
        simpa only [heq] using hl
      have hend' : upper (vertices (start + 1 + (distance - 1) + length)) = true := by
        simpa only [heq] using hend
      have h := ih (start := start + 1) (distance := distance - 1)
        (by omega) (by omega) hu' hl' hend'
      simpa only [heq] using h

end Queens.Finite
