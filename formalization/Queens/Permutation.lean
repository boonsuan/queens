import Queens.Greedy
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Every row contains a greedy queen

Section 2, Lemma 3 is proved by the paper's antidiagonal argument. Distinct
natural coordinates have a quadratic lower bound on their sum, so occupied
antidiagonals cannot contain a tail of the natural numbers. A least missing
row would force such a tail.
-/

namespace Queens

/-- Distinct natural numbers have sum at least `0 + ⋯ + (card - 1)`,
written without division. This is the counting estimate in Lemma 3. -/
theorem card_mul_pred_le_twice_sum (s : Finset ℕ) :
    s.card * (s.card - 1) ≤ 2 * ∑ i ∈ s, i := by
  have hsum : (∑ i ∈ Finset.range s.card, i) ≤ ∑ i ∈ s, i := by
    have h := Finset.sum_range_le_sum
      (s := s.image (fun n : ℕ => (n : ℤ))) (c := 0) (by
        intro x hx
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
        exact Int.natCast_nonneg n)
    rw [Finset.card_image_of_injective _ Nat.cast_injective] at h
    rw [Finset.sum_image (fun a _ b _ hab => Nat.cast_injective hab)] at h
    simp only [zero_add] at h
    rw [← Nat.cast_sum, ← Nat.cast_sum] at h
    exact_mod_cast h
  have hformula := Finset.sum_range_id_mul_two s.card
  omega

/-- The same coordinate-sum estimate for an injective enumeration, as used
for both columns and rows in the proof of Lemma 3. -/
theorem range_mul_pred_le_twice_sum (f : ℕ → ℕ) (hf : Function.Injective f) (t : ℕ) :
    t * (t - 1) ≤ 2 * ∑ i ∈ Finset.range t, f i := by
  have h := card_mul_pred_le_twice_sum ((Finset.range t).image f)
  rw [Finset.card_image_of_injective _ hf, Finset.card_range,
    Finset.sum_image (fun a _ b _ hab => hf hab)] at h
  exact h

/-- The occupied antidiagonals cannot contain a tail of the natural
numbers. This is the coordinate-sum contradiction in Section 2, Lemma 3. -/
theorem no_antidiagonal_tail : ¬ ∃ N, ∀ s ≥ N, ∃ i, q i + i = s := by
  rintro ⟨N, hN⟩
  have hex : ∀ k, ∃ i, q i + i = N + k := fun k => hN (N + k) (by omega)
  choose a ha using hex
  have ha_inj : Function.Injective a := by
    intro i j hij
    have hi := ha i
    have hj := ha j
    rw [hij] at hi
    omega
  let t := 2 * N + 2
  have hcols := range_mul_pred_le_twice_sum a ha_inj t
  have hrows := range_mul_pred_le_twice_sum (q ∘ a) (q_injective.comp ha_inj) t
  have hsum : (∑ i ∈ Finset.range t, q (a i)) + (∑ i ∈ Finset.range t, a i) =
      t * N + ∑ i ∈ Finset.range t, i := by
    rw [← Finset.sum_add_distrib]
    simp_rw [ha]
    rw [Finset.sum_add_distrib]
    simp
  have hformula := Finset.sum_range_id_mul_two t
  have ht : t - 1 = 2 * N + 1 := by omega
  dsimp only [Function.comp_def] at hrows
  rw [ht] at hcols hrows hformula
  dsimp only [t] at hcols hrows hsum hformula
  nlinarith

/-- If a row is missing but all smaller rows are occupied, then all
sufficiently large antidiagonals are occupied. This is the first half of
the proof of Section 2, Lemma 3. -/
theorem missing_row_forces_antidiagonal_tail {m : ℕ}
    (hmissing : ∀ i, q i ≠ m) (hsmall : ∀ r < m, ∃ i, q i = r) :
    ∃ N, ∀ s ≥ N, ∃ i, q i + i = s := by
  classical
  have hex : ∀ r : Fin m, ∃ i, q i = r.val := fun r => hsmall r.val r.isLt
  choose col hcol using hex
  let C := ∑ r : Fin m, col r
  have hbound (r : Fin m) : col r ≤ C :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (col i)) (Finset.mem_univ r)
  refine ⟨C + 2 * m + 1, ?_⟩
  intro s hs
  let n := s - m
  have hn : C + m < n := by dsimp [n]; omega
  have hnm : n + m = s := by dsimp [n]; omega
  have hq : m < q n := by
    by_contra h
    have hqm : q n < m := by
      have hne := hmissing n
      omega
    let r : Fin m := ⟨q n, hqm⟩
    have hsame : col r = n := q_injective (hcol r)
    have hb := hbound r
    omega
  have hnot : ¬ Available n m (fun i => q i.val) := by
    intro havailable
    have hle := q_le_of_available havailable
    omega
  simp only [Available, not_forall, not_and_or, not_not] at hnot
  obtain ⟨i, hrow | hdiag | hanti⟩ := hnot
  · exact False.elim (hmissing i.val hrow.symm)
  · have hqi : q i.val < m := by have hi := i.isLt; omega
    let r : Fin m := ⟨q i.val, hqi⟩
    have hsame : col r = i.val := q_injective (hcol r)
    have hb := hbound r
    omega
  · exact ⟨i.val, by omega⟩

/-- **Lemma 3 (surjectivity).** Every natural row contains a greedy queen.
Together with `q_injective`, this says that `q` is a permutation of `ℕ`. -/
theorem q_surjective : Function.Surjective q := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_contra hmissing
    have hmiss : ∀ i, q i ≠ m := by simpa only [not_exists] using hmissing
    exact no_antidiagonal_tail (missing_row_forces_antidiagonal_tail hmiss ih)

/-- **Lemma 3 (permutation).** The greedy queens sequence is a bijection
between the natural column indices and the natural row indices. -/
theorem q_bijective : Function.Bijective q := ⟨q_injective, q_surjective⟩

end Queens
