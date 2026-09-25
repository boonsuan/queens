import Queens.Greedy
import Mathlib.Data.Nat.Bitwise

/-!
# Efficient certificates for finite greedy prefixes

The attainment part of Corollary 19 requires actual queens, rather than paths
merely allowed by the finite graph. The checker here maintains the three attack
masks of the defining greedy rule. Its correctness is proved for arbitrary
prefixes; the numerical certificate is supplied separately.
-/

namespace Queens.Finite

/-- Corollary 19, attainment checks: the attacked rows in the current column,
separated into horizontal, upward-diagonal, and downward-diagonal attacks. -/
structure AttackBoard where
  /-- Rows already occupied by an earlier queen. -/
  rows : ℕ
  /-- Attacks whose row increases when the column increases. -/
  rising : ℕ
  /-- Attacks whose row decreases when the column increases. -/
  falling : ℕ
  deriving DecidableEq

/-- Corollary 19: the initially empty bitboard, before the queen at the origin. -/
def AttackBoard.empty : AttackBoard := ⟨0, 0, 0⟩

/-- Corollary 19: place a queen and advance to the next column. -/
def AttackBoard.advance (b : AttackBoard) (r : ℕ) : AttackBoard :=
  ⟨b.rows ||| 2 ^ r, (b.rising ||| 2 ^ r) <<< 1,
    (b.falling ||| 2 ^ r) >>> 1⟩

/-- Corollary 19: the union of the three attack masks. -/
def AttackBoard.attacks (b : AttackBoard) : ℕ := b.rows ||| b.rising ||| b.falling

/-- Corollary 19: a proposed queen is unattacked and all smaller rows are
attacked. The bit-mask equality checks every smaller row simultaneously. -/
def AttackBoard.checkRow (b : AttackBoard) (r : ℕ) : Bool :=
  !(b.attacks.testBit r) && (b.attacks &&& (2 ^ r - 1) == 2 ^ r - 1)

/-- Corollary 19: verify every entry of a proposed prefix by the greedy rule. -/
def AttackBoard.checkRows (b : AttackBoard) : List ℕ → Bool
  | [] => true
  | r :: rs => b.checkRow r && (b.advance r).checkRows rs

/-- Corollary 19: a bitboard represents precisely the attacks of the actual
queens strictly before column `n`. -/
def AttackBoard.Represents (b : AttackBoard) (n : ℕ) : Prop :=
  (∀ r, b.rows.testBit r = true ↔ ∃ i < n, r = q i) ∧
  (∀ r, b.rising.testBit r = true ↔ ∃ i < n, r + i = q i + n) ∧
  (∀ r, b.falling.testBit r = true ↔ ∃ i < n, r + n = q i + i)

/-- For Corollary 19, the empty board represents the defining greedy process before column zero. -/
theorem AttackBoard.empty_represents : AttackBoard.empty.Represents 0 := by
  simp [Represents, empty]

/-- For Corollary 19, advancing a represented attack board with the actual queen preserves its
interpretation. This justifies the shifts in the finite prefix checker. -/
theorem AttackBoard.Represents.advance {b : AttackBoard} {n : ℕ}
    (h : b.Represents n) : (b.advance (q n)).Represents (n + 1) := by
  rcases h with ⟨hrows, hrising, hfalling⟩
  constructor
  · intro r
    simp only [AttackBoard.advance, Nat.testBit_or, Bool.or_eq_true,
      Nat.testBit_two_pow, decide_eq_true_eq, hrows]
    constructor
    · rintro (⟨i, hi, hr⟩ | hr)
      · exact ⟨i, by omega, hr⟩
      · exact ⟨n, by omega, hr.symm⟩
    · rintro ⟨i, hi, hr⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, hr⟩
      · right
        have : i = n := by omega
        simpa [this] using hr.symm
  constructor
  · intro r
    simp only [AttackBoard.advance, Nat.testBit_shiftLeft, Nat.testBit_or,
      Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Nat.testBit_two_pow,
      hrising]
    constructor
    · rintro ⟨hr, (⟨i, hi, heq⟩ | heq)⟩
      · exact ⟨i, by omega, by omega⟩
      · exact ⟨n, by omega, by omega⟩
    · rintro ⟨i, hi, heq⟩
      have hr : 1 ≤ r := by omega
      refine ⟨hr, ?_⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, by omega⟩
      · right
        have : i = n := by omega
        subst i
        omega
  · intro r
    simp only [AttackBoard.advance, Nat.testBit_shiftRight, Nat.testBit_or,
      Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq, hfalling]
    constructor
    · rintro (⟨i, hi, heq⟩ | heq)
      · exact ⟨i, by omega, by omega⟩
      · exact ⟨n, by omega, by omega⟩
    · rintro ⟨i, hi, heq⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, by omega⟩
      · right
        have : i = n := by omega
        subst i
        omega

/-- For Corollary 19, on a represented board, a clear bit is exactly an available row in the
original least-unattacked-row definition. -/
theorem AttackBoard.Represents.available_iff {b : AttackBoard} {n : ℕ}
    (h : b.Represents n) (r : ℕ) :
    Available n r (fun i => q i.val) ↔ b.attacks.testBit r = false := by
  rcases h with ⟨hr, hd, ha⟩
  have hbit : b.attacks.testBit r = true ↔
      (∃ i < n, r = q i) ∨ (∃ i < n, r + i = q i + n) ∨
        (∃ i < n, r + n = q i + i) := by
    simp [AttackBoard.attacks, hr, hd, ha, or_assoc]
  rw [← Bool.not_eq_true, hbit]
  simp only [Available, not_or, not_exists, not_and]
  constructor
  · intro h
    exact ⟨fun i hi => (h ⟨i, hi⟩).1,
      fun i hi => (h ⟨i, hi⟩).2.1, fun i hi => (h ⟨i, hi⟩).2.2⟩
  · rintro ⟨hr, hd, ha⟩ i
    exact ⟨hr i.val i.isLt, hd i.val i.isLt, ha i.val i.isLt⟩

/-- For Corollary 19, a successfully checked row on a represented board is the actual greedy
choice, not just a legal nonattacking placement. -/
theorem AttackBoard.Represents.eq_q_of_checkRow {b : AttackBoard} {n r : ℕ}
    (h : b.Represents n) (hc : b.checkRow r = true) : r = q n := by
  have hc' : b.attacks.testBit r = false ∧
      b.attacks &&& (2 ^ r - 1) = 2 ^ r - 1 := by
    simpa [AttackBoard.checkRow] using hc
  have hle : q n ≤ r := q_le_of_available ((h.available_iff r).mpr hc'.1)
  apply Nat.le_antisymm _ hle
  by_contra hsmall
  have hqr : q n < r := by omega
  have hb := congrArg (fun m : ℕ => m.testBit (q n)) hc'.2
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, hqr, decide_true,
    Bool.and_true] at hb
  have hav := (h.available_iff (q n)).mp (q_available n)
  simp [hav] at hb

/-- For Corollary 19, every entry of a successfully checked list agrees with the actual greedy
sequence, beginning at the column represented by its initial attack board. -/
theorem AttackBoard.Represents.q_eq_of_checkRows {b : AttackBoard} {n : ℕ}
    (h : b.Represents n) {rows : List ℕ} (hc : b.checkRows rows = true) :
    ∀ i : Fin rows.length, q (n + i.val) = rows[i] := by
  induction rows generalizing b n with
  | nil => intro i; exact Fin.elim0 i
  | cons r rs ih =>
    simp only [AttackBoard.checkRows, Bool.and_eq_true] at hc
    have heq := h.eq_q_of_checkRow hc.1
    have hnext : (b.advance r).Represents (n + 1) := by rw [heq]; exact h.advance
    intro i
    cases i using Fin.cases with
    | zero => simpa using heq.symm
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hnext hc.2 i

end Queens.Finite
