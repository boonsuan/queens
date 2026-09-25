import Queens.Finite.RepeatedRunChecks

/-!
# Soundness of the checked repeated-run certificate

This file turns the finite kernel checks into the generic labeled-path
certificate used for the third row of Corollary 19.
-/

namespace Queens.Finite

/-- Every original state index has a corresponding run-certificate entry. -/
theorem repeatedRunTree_lookup_exists {v : ℕ} (hv : v < FortyData.states.size) :
    ∃ entry, indexedLookup v repeatedRunTree = some entry := by
  have hself : ∀ e ∈ indexedEntries repeatedRunTree,
      indexedLookup e.1 repeatedRunTree = some e.2 := by
    intro e he
    exact of_decide_eq_true (indexedAll_eq_true.mp repeatedRunTree_self_lookup e he)
  obtain ⟨a, ha, _⟩ := indexedLookup_of_list_alignment (field := RunVertexData.upper) hself
    repeatedRunTree_upper_alignment
    (show v < (FortyData.states.toList.map
      (fun s => decide (upperBit (s.output % 4) = 1))).length by simpa using hv)
  exact ⟨a, ha⟩

/-- Corollary 19: the fast upper bit is the actual output bit of the numbered
state in the original forty-symbol certificate. -/
theorem fortyStateUpper_eq {v : ℕ} (hv : v < FortyData.states.size) :
    fortyStateUpper v = decide (upperBit (FortyData.states[v].output % 4) = 1) := by
  obtain ⟨a, ha⟩ := repeatedRunTree_lookup_exists hv
  have h := indexedLookup_field_eq_getElem? (field := RunVertexData.upper)
    repeatedRunTree_upper_alignment ha
  simp [hv] at h
  simpa [fortyStateUpper, ha] using h.symm

/-- Appendix A: the fast run-graph adjacency agrees with every successor list
used in the independently checked forty-symbol state graph. -/
theorem fortyRunAdjacency_eq {v : ℕ} (hv : v < FortyData.states.size) :
    fortyRunAdjacency v = FortyData.successors[v]?.getD [] := by
  obtain ⟨a, ha⟩ := repeatedRunTree_lookup_exists hv
  have h := indexedLookup_field_eq_getElem? (field := RunVertexData.successors)
    repeatedRunTree_successor_alignment ha
  simpa [fortyRunAdjacency, ha] using (congrArg (fun o => o.getD []) h).symm

private theorem repeatedRunVertex_checked {v : ℕ}
    (hexists : ∃ entry, indexedLookup v repeatedRunTree = some entry)
    (hu : fortyStateUpper v = true) : CheckRepeatedRunVertex v := by
  obtain ⟨entry, he⟩ := hexists
  have hmem := indexedLookup_mem he
  have h := of_decide_eq_true (indexedAll_eq_true.mp repeatedRunLengthData_checked (v, entry) hmem)
  apply h
  simpa [fortyStateUpper, he] using hu

/-- Corollary 19: the finite checks instantiate the generic, proved certificate
for runs in a labeled walk. The allowed set here is the union needed by A275887. -/
def repeatedRunCertificate : Sequence.RunLengthCertificate FortyRunEdge {1, 2, 3}
    (fun _ => {k | AllowedRepeatedRunLength k}) where
  lengths c v := (repeatedRunLengths c v).toFinset
  terminal := by
    intro v w c d hc he hd
    rcases he with ⟨hv, hu, he⟩
    have hcheck := (repeatedRunVertex_checked hv hu).2 (w, d) he
    have hc' : c ∈ ([1, 2, 3] : List ℕ) := by simpa using hc
    simpa using (hcheck c hc').2 hd |>.1
  prepend := by
    intro v w c k hc he hk
    rcases he with ⟨hv, hu, he⟩
    have hcheck := (repeatedRunVertex_checked hv hu).2 (w, c) he
    have hc' : c ∈ ([1, 2, 3] : List ℕ) := by simpa using hc
    have hk' : k ∈ repeatedRunLengths c w := by simpa using hk
    simpa using (hcheck c hc').1 rfl k hk'
  starts := by
    intro u v c d k hc he hd hk hkpos
    rcases he with ⟨hu, hup, he⟩
    have hcheck := (repeatedRunVertex_checked hu hup).2 (v, d) he
    have hc' : c ∈ ([1, 2, 3] : List ℕ) := by simpa using hc
    have hk' : k ∈ repeatedRunLengths c v := by simpa using hk
    exact (hcheck c hc').2 hd |>.2 k hk' hkpos


/-- Corollary 19: every upper-state certificate has a possible remaining
length for each run label. This rules out a constant infinite tail rather than
merely restricting already-terminated runs. -/
theorem repeatedRunLengths_nonempty {v c : ℕ}
    (hv : ∃ entry, indexedLookup v repeatedRunTree = some entry)
    (hu : fortyStateUpper v = true) (hc : c ∈ ({1, 2, 3} : Finset ℕ)) :
    (repeatedRunCertificate.lengths c v).Nonempty := by
  have hc' : c ∈ ([1, 2, 3] : List ℕ) := by simpa using hc
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ ((repeatedRunVertex_checked hv hu).1 c hc').1
  exact ⟨k, by simpa [repeatedRunCertificate] using hk⟩

/-- Corollary 19: all remaining lengths in an upper-state certificate are at
most eleven, supplying a uniform bound on constant-labeled finite paths. -/
theorem repeatedRunLengths_le_eleven {v c k : ℕ}
    (hv : ∃ entry, indexedLookup v repeatedRunTree = some entry)
    (hu : fortyStateUpper v = true) (hc : c ∈ ({1, 2, 3} : Finset ℕ))
    (hk : k ∈ repeatedRunCertificate.lengths c v) : k ≤ 11 := by
  have hc' : c ∈ ([1, 2, 3] : List ℕ) := by simpa using hc
  exact ((repeatedRunVertex_checked hv hu).1 c hc').2 k (by
    simpa [repeatedRunCertificate] using hk)

end Queens.Finite
