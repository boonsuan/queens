import Mathlib.Data.Finset.Range

/-!
# Maximal runs and gaps in a predicate on the natural numbers

These sequence notions give the meaning of the five rows of Corollary 19.
Indices start at zero. A run at the start of a sequence needs no left-hand
boundary; all other runs are bounded on both sides by failure of the predicate.
-/

namespace Queens.Sequence

/-- Corollary 19: a nonempty maximal run of a predicate, specified by its first
index and length. The left boundary is omitted only at index zero. -/
def MaximalRun (p : ℕ → Prop) (start length : ℕ) : Prop :=
  0 < length ∧ (∀ i : Fin length, p (start + i.val)) ∧
    (start = 0 ∨ ¬p (start - 1)) ∧ ¬p (start + length)

/-- For Corollary 19, a finite maximal-run assertion is decidable when its
predicate is decidable. -/
instance {p : ℕ → Prop} [DecidablePred p] (start length : ℕ) :
    Decidable (MaximalRun p start length) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every index inside a maximal run satisfies its predicate. This interval
interface avoids arithmetic on `Fin` indices in Corollary 19's coverage proofs. -/
theorem MaximalRun.mem {p : ℕ → Prop} {start length n : ℕ}
    (h : MaximalRun p start length) (hstart : start ≤ n) (hend : n < start + length) :
    p n := by
  have hm := h.2.1 ⟨n - start, by omega⟩
  simpa only [Nat.add_sub_of_le hstart] using hm

/-- The first term of a maximal run satisfies its predicate. In Corollary 19,
this identifies the repeated value from the first lower-run length. -/
theorem MaximalRun.first {p : ℕ → Prop} {start length : ℕ}
    (h : MaximalRun p start length) : p start :=
  h.mem le_rfl (by have := h.1; omega)

/-- Corollary 19: two consecutive occurrences of a predicate, specified by the
first occurrence and their positive difference. -/
def ConsecutiveGap (p : ℕ → Prop) (start gap : ℕ) : Prop :=
  0 < gap ∧ p start ∧ p (start + gap) ∧
    ∀ i : Fin gap, 0 < i.val → ¬p (start + i.val)

/-- For Corollary 19, a finite consecutive-gap assertion is decidable for a decidable predicate. -/
instance {p : ℕ → Prop} [DecidablePred p] (start gap : ℕ) :
    Decidable (ConsecutiveGap p start gap) := inferInstanceAs (Decidable (_ ∧ _))

/-- Corollary 19: forbidding a constant block of length `bound + 1` bounds
every maximal run by `bound`. -/
theorem MaximalRun.length_le {p : ℕ → Prop} {bound start length : ℕ}
    (hblock : ∀ s, ¬∀ i : Fin (bound + 1), p (s + i.val))
    (h : MaximalRun p start length) : length ≤ bound := by
  by_contra hlong
  apply hblock start
  intro i
  exact h.2.1 ⟨i.val, by omega⟩

/-- Corollary 19: a gap contains one fewer consecutive failures of the
predicate. A forbidden complementary block therefore bounds the gap. -/
theorem ConsecutiveGap.length_le {p : ℕ → Prop} {bound start gap : ℕ}
    (hblock : ∀ s, ¬∀ i : Fin bound, ¬p (s + i.val))
    (h : ConsecutiveGap p start gap) : gap ≤ bound := by
  by_contra hlong
  apply hblock (start + 1)
  intro i
  have hi := i.isLt
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    h.2.2.2 ⟨i.val + 1, by omega⟩ (Nat.succ_pos i.val)

/-- For Corollary 19, maximal-run assertions only depend on the predicate up to their right
boundary. This transfers computed occurrence witnesses to an infinite sequence. -/
theorem maximalRun_congr {p q : ℕ → Prop} {start length : ℕ}
    (h : ∀ i ≤ start + length, p i ↔ q i) :
    MaximalRun p start length ↔ MaximalRun q start length := by
  simp only [MaximalRun]
  have hbody : (∀ i : Fin length, p (start + i.val)) ↔
      ∀ i : Fin length, q (start + i.val) := by
    apply forall_congr'
    intro i
    exact h _ (by omega)
  rw [hbody, h (start - 1) (by omega), h (start + length) le_rfl]

/-- For Corollary 19, consecutive-gap assertions only depend on the predicate up to their second
endpoint. This transfers a computed gap to the infinite sequence. -/
theorem consecutiveGap_congr {p q : ℕ → Prop} {start gap : ℕ}
    (h : ∀ i ≤ start + gap, p i ↔ q i) :
    ConsecutiveGap p start gap ↔ ConsecutiveGap q start gap := by
  simp only [ConsecutiveGap]
  have hbody : (∀ i : Fin gap, 0 < i.val → ¬p (start + i.val)) ↔
      ∀ i : Fin gap, 0 < i.val → ¬q (start + i.val) := by
    apply forall_congr'
    intro i
    rw [h _ (by omega)]
  rw [hbody, h start (by omega), h (start + gap) le_rfl]

/-- For Corollary 19, two maximal runs of the same predicate with the same start have the same
length: the shorter right boundary would otherwise lie inside the longer run. -/
theorem MaximalRun.length_unique {p : ℕ → Prop} {start a b : ℕ}
    (ha : MaximalRun p start a) (hb : MaximalRun p start b) : a = b := by
  apply Nat.le_antisymm
  · by_contra h
    exact hb.2.2.2 (ha.2.1 ⟨b, by omega⟩)
  · by_contra h
    exact ha.2.2.2 (hb.2.1 ⟨a, by omega⟩)

/-- For Corollary 19, dropping an initial prefix preserves every maximal run that starts at or
after the cut. A run starting exactly at the cut becomes an initial run. -/
theorem MaximalRun.shift {p : ℕ → Prop} {start length offset : ℕ}
    (h : MaximalRun p start length) (hoffset : offset ≤ start) :
    MaximalRun (fun n => p (offset + n)) (start - offset) length := by
  have heq : offset + (start - offset) = start := by omega
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro i
    simpa [← Nat.add_assoc, heq] using h.2.1 i
  · by_cases hs : start - offset = 0
    · exact Or.inl hs
    · right
      have hspos : start ≠ 0 := by omega
      have heq' : offset + (start - offset - 1) = start - 1 := by omega
      simpa only [heq'] using h.2.2.1.resolve_left hspos
  · simpa [← Nat.add_assoc, heq] using h.2.2.2

end Queens.Sequence
