import Queens.Runs

/-!
# Certificates for runs in a labeled graph walk

Corollary 19 reduces repeated lower-run lengths to a walk in a finite labeled
graph. The certificate used here assigns to each vertex the permitted numbers
of equal labels before a different label. Checking closure under prepending one
edge is sufficient: induction on an actual finite path proves the bound. A
particular topological-sort implementation is not part of the trusted argument.
The path and certificate interfaces allow arbitrary vertex and label types.
-/

namespace Queens.Sequence

variable {V Label : Type*}

/-- Corollary 19: a finite path all of whose edges carry one fixed label. -/
inductive ConstantLabelPath (edge : V → Label → V → Prop) (label : Label) : V → ℕ → V → Prop
  | nil (v : V) : ConstantLabelPath edge label v 0 v
  | cons {v w t : V} {length : ℕ} : edge v label w →
      ConstantLabelPath edge label w length t →
      ConstantLabelPath edge label v (length + 1) t

/-- Corollary 19: a walk with separately specified vertices and edge labels. -/
def LabeledWalk (edge : V → Label → V → Prop) (vertices : ℕ → V)
    (labels : ℕ → Label) : Prop := ∀ n, edge (vertices n) (labels n) (vertices (n + 1))

/-- For Corollary 19, a constant block in the labels of a walk gives a constant-labeled finite
path between the corresponding vertices. -/
theorem LabeledWalk.constantLabelPath {edge : V → Label → V → Prop}
    {vertices : ℕ → V} {labels : ℕ → Label} (hwalk : LabeledWalk edge vertices labels)
    {start length : ℕ} {label : Label} (h : ∀ i : Fin length, labels (start + i.val) = label) :
    ConstantLabelPath edge label (vertices start) length (vertices (start + length)) := by
  induction length generalizing start with
  | zero => simpa using ConstantLabelPath.nil (edge := edge) (label := label) (vertices start)
  | succ length ih =>
    have he := hwalk start
    have hz := h 0
    simp only [Fin.val_zero, Nat.add_zero] at hz
    rw [hz] at he
    have htail : ∀ i : Fin length, labels (start + 1 + i.val) = label := by
      intro i
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h i.succ
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ConstantLabelPath.cons he (ih htail)

/-- Corollary 19: finite sets of possible lengths before a differently labeled
edge. Only closure of these sets is needed, not an untrusted claim that they
were computed exhaustively. `starts` handles the other boundary of a maximal run. -/
structure RunLengthCertificate (edge : V → Label → V → Prop)
    (labels : Finset Label) (allowed : Label → Set ℕ) where
  /-- For Corollary 19, permitted numbers of `c`-edges before a first differently labeled edge. -/
  lengths : Label → V → Finset ℕ
  /-- A different next edge terminates a constant path of length zero. -/
  terminal : ∀ {v w c d}, c ∈ labels → edge v d w → d ≠ c → 0 ∈ lengths c v
  /-- Prepending a `c`-edge increases a permitted remaining length by one. -/
  prepend : ∀ {v w c k}, c ∈ labels → edge v c w →
    k ∈ lengths c w → k + 1 ∈ lengths c v
  /-- A positive length following a different preceding edge has an allowed value. -/
  starts : ∀ {u v c d k}, c ∈ labels → edge u d v → d ≠ c →
    k ∈ lengths c v → 0 < k → k ∈ allowed c

/-- For Corollary 19, prepending a constant path to a certified remaining length adds their
lengths. No different final label is required for this closure lemma. -/
theorem RunLengthCertificate.path_add_mem {edge : V → Label → V → Prop}
    {labels : Finset Label} {allowed : Label → Set ℕ}
    (cert : RunLengthCertificate edge labels allowed)
    {v w : V} {c : Label} {length k : ℕ} (hc : c ∈ labels)
    (hpath : ConstantLabelPath edge c v length w) (hk : k ∈ cert.lengths c w) :
    length + k ∈ cert.lengths c v := by
  induction hpath with
  | nil => simpa using hk
  | cons he _ ih =>
    have h := cert.prepend hc he (ih hk)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The closure checks in a run-length certificate are sound for every finite
constant-labeled path that ends at a differently labeled edge. -/
theorem RunLengthCertificate.path_length_mem {edge : V → Label → V → Prop}
    {labels : Finset Label} {allowed : Label → Set ℕ}
    (cert : RunLengthCertificate edge labels allowed)
    {v w t : V} {c d : Label} {length : ℕ} (hc : c ∈ labels)
    (hpath : ConstantLabelPath edge c v length w) (hend : edge w d t) (hd : d ≠ c) :
    length ∈ cert.lengths c v := by
  simpa using cert.path_add_mem hc hpath (cert.terminal hc hend hd)

/-- **Corollary 19, graph argument:** every positive-start maximal run in a
walk has a length allowed by a checked certificate. Runs at index zero need
separate initial-state information, just as the paper checks its initial runs. -/
theorem RunLengthCertificate.maximalRun_length_mem {edge : V → Label → V → Prop}
    {labels : Finset Label} {allowed : Label → Set ℕ}
    (cert : RunLengthCertificate edge labels allowed)
    {vertices : ℕ → V} {word : ℕ → Label} (hwalk : LabeledWalk edge vertices word)
    {start length : ℕ} {c : Label} (hc : c ∈ labels) (hs : 0 < start)
    (hrun : MaximalRun (fun n => word n = c) start length) : length ∈ allowed c := by
  have hpath := hwalk.constantLabelPath hrun.2.1
  have hmem := cert.path_length_mem hc hpath (hwalk (start + length)) hrun.2.2.2
  have hpre : word (start - 1) ≠ c := hrun.2.2.1.resolve_left (by omega)
  have he := hwalk (start - 1)
  have heq : start - 1 + 1 = start := by omega
  rw [heq] at he
  exact cert.starts hc he hpre hmem hrun.1

/-- For Corollary 19, nonempty bounded remaining-length sets bound all constant paths, including
prefixes of an infinite constant tail. This justifies termination of every run. -/
theorem RunLengthCertificate.constantPath_length_le {edge : V → Label → V → Prop}
    {labels : Finset Label} {allowed : Label → Set ℕ}
    (cert : RunLengthCertificate edge labels allowed)
    {v w : V} {c : Label} {length bound : ℕ} (hc : c ∈ labels)
    (hpath : ConstantLabelPath edge c v length w)
    (hend : (cert.lengths c w).Nonempty)
    (hbound : ∀ k ∈ cert.lengths c v, k ≤ bound) : length ≤ bound := by
  obtain ⟨k, hk⟩ := hend
  have h := hbound _ (cert.path_add_mem hc hpath hk)
  omega

end Queens.Sequence
