import Queens.Greedy

/-!
# The actual queen word

Definition 9 in Section 4.2 of *Greedy Queens and the Golden Ratio* encodes
upper columns and upper rows as symbols `2u + b`. These definitions refer to
the actual greedy sequence, independently of the finite-state calculation.
-/

namespace Queens

/-- Definition 9: `uₙ`, the indicator of an upper queen in column `n`. -/
noncomputable def columnBit (n : ℕ) : ℕ := if n < q n then 1 else 0

/-- Definition 9: `bₙ`, the indicator of an upper queen in row `n`.
An upper queen in row `n` must occur before column `n`, so the test is finite. -/
noncomputable def upperRowBit (n : ℕ) : ℕ :=
  if ∃ i : Fin n, i.val < q i.val ∧ q i.val = n then 1 else 0

/-- Definition 9: the actual symbol `σₙ = 2uₙ + bₙ`.
The paper uses positive indices; the harmless extension at zero is also defined. -/
noncomputable def queenSymbol (n : ℕ) : ℕ := 2 * columnBit n + upperRowBit n

/-- Definition 9: the column indicator is a bit. -/
theorem columnBit_le_one (n : ℕ) : columnBit n ≤ 1 := by
  unfold columnBit
  split <;> omega

/-- Definition 9: the row indicator is a bit. -/
theorem upperRowBit_le_one (n : ℕ) : upperRowBit n ≤ 1 := by
  unfold upperRowBit
  split <;> omega

/-- Definition 9: the queen word takes values in the four-symbol alphabet. -/
theorem queenSymbol_lt_four (n : ℕ) : queenSymbol n < 4 := by
  have hu := columnBit_le_one n
  have hb := upperRowBit_le_one n
  unfold queenSymbol
  omega

/-- Definition 9: a row bit is one exactly when an upper queen occupies that row. -/
theorem upperRowBit_eq_one_iff (n : ℕ) :
    upperRowBit n = 1 ↔ ∃ i : ℕ, i < q i ∧ q i = n := by
  simp only [upperRowBit, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  constructor
  · rintro ⟨i, hi, hn⟩
    exact ⟨i.val, hi, hn⟩
  · rintro ⟨i, hi, hn⟩
    exact ⟨⟨i, by omega⟩, hi, hn⟩

end Queens
