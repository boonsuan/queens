import Queens.Runs
import Mathlib.Data.Nat.Find

/-!
# Coverage by finite maximal runs

Corollary 19 treats runs as consecutive terms of a sequence. A bound on
constant blocks ensures that every occurrence belongs to a finite maximal run;
the range statements therefore do not overlook a possible infinite final run.
The lemmas here apply to any predicate on the natural numbers.
-/

namespace Queens.Sequence

/-- Two maximal runs containing the same index are the same interval.
This is the uniqueness needed when interpreting the run sequences of Corollary 19. -/
theorem MaximalRun.eq_of_contains {p : ℕ → Prop} {a b l m n : ℕ}
    (ha : MaximalRun p a l) (hb : MaximalRun p b m)
    (han : a ≤ n) (hnal : n < a + l) (hbn : b ≤ n) (hnbm : n < b + m) :
    a = b ∧ l = m := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim (hb.2.2.1.resolve_left (by omega)
        (ha.mem (by omega) (by omega)))
    · exact heq
    · exact False.elim (ha.2.2.1.resolve_left (by omega)
        (hb.mem (by omega) (by omega)))
  subst b
  exact ⟨rfl, ha.length_unique hb⟩

/-- If arbitrarily placed blocks of a fixed length cannot all satisfy a
predicate, every occurrence lies in a unique finite maximal run. Applied to
Corollary 19, this excludes an infinite final run from the sequence interpretation. -/
theorem existsUnique_maximalRun_contains {p : ℕ → Prop} {bound n : ℕ}
    (hblock : ∀ s, ¬∀ i : Fin (bound + 1), p (s + i.val)) (hn : p n) :
    ∃! interval : ℕ × ℕ, MaximalRun p interval.1 interval.2 ∧
      interval.1 ≤ n ∧ n < interval.1 + interval.2 := by
  classical
  have hleft : ∃ s, s ≤ n ∧ ∀ j, s ≤ j → j ≤ n → p j := by
    refine ⟨n, le_rfl, ?_⟩
    intro j hnj hjn
    have : j = n := by omega
    simpa only [this] using hn
  let s := Nat.find hleft
  have hs : s ≤ n ∧ ∀ j, s ≤ j → j ≤ n → p j := Nat.find_spec hleft
  have hright : ∃ t, n ≤ t ∧ ¬p t := by
    obtain ⟨i, hi⟩ := not_forall.mp (hblock n)
    exact ⟨n + i.val, by omega, hi⟩
  let t := Nat.find hright
  have ht : n ≤ t ∧ ¬p t := Nat.find_spec hright
  have hnt : n < t := by
    by_contra h
    have : t = n := by omega
    exact ht.2 (this.symm ▸ hn)
  have hp : ∀ j, s ≤ j → j < t → p j := by
    intro j hsj hjt
    by_cases hjn : j ≤ n
    · exact hs.2 j hsj hjn
    · by_contra hj
      exact Nat.find_min hright hjt ⟨by omega, hj⟩
  have hrun : MaximalRun p s (t - s) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i
      have hi := i.isLt
      exact hp (s + i.val) (by omega) (by omega)
    · by_cases hzero : s = 0
      · exact Or.inl hzero
      · right
        intro hprev
        apply Nat.find_min hleft (by omega : s - 1 < s)
        refine ⟨by omega, ?_⟩
        intro j hsj hjn
        by_cases heq : j = s - 1
        · simpa only [heq] using hprev
        · exact hs.2 j (by omega) hjn
    · have heq : s + (t - s) = t := by omega
      simpa only [heq] using ht.2
  refine ⟨(s, t - s), ⟨hrun, hs.1, by omega⟩, ?_⟩
  rintro ⟨a, l⟩ ⟨ha, han, hnal⟩
  obtain ⟨rfl, rfl⟩ := ha.eq_of_contains hrun han hnal hs.1 (by omega)
  rfl

end Queens.Sequence
