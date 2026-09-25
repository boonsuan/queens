import Queens.Finite.Local
import Mathlib.Tactic.Ring

/-!
# Exactness of history encodings

Definition 11 uses fixed-length words in base four. These kernel-checked lemmas
connect the executable history representation to ordinary lists of symbols;
they do not depend on the computational certificate.
-/

namespace Queens.Finite

/-- Definition 11: decoding always produces the specified number of symbols. -/
@[simp] theorem decode_length (code length : ℕ) : (decode code length).length = length := by
  induction length generalizing code with
  | zero => rfl
  | succ length ih => simp [decode, ih]

/-- Definition 11: appending one symbol is one base-four accumulation step. -/
theorem encode_append_singleton (word : List ℕ) (symbol : ℕ) :
    encode (word ++ [symbol]) = 4 * encode word + symbol := by
  simp [encode, List.foldl_append]

/-- Definition 11: the base-four encoding and fixed-length decoding are inverse
on words over the paper's alphabet `{0,1,2,3}`. -/
theorem decode_encode {word : List ℕ} (hword : ∀ symbol ∈ word, symbol < 4) :
    decode (encode word) word.length = word := by
  induction word using List.reverseRecOn with
  | nil => rfl
  | append_singleton word symbol ih =>
      have hs : symbol < 4 := hword symbol (by simp)
      have hw : ∀ s ∈ word, s < 4 := fun s h => hword s (by simp [h])
      rw [List.length_append, List.length_singleton, encode_append_singleton, decode]
      have hdiv : (4 * encode word + symbol) / 4 = encode word := by omega
      have hmod : (4 * encode word + symbol) % 4 = symbol := by omega
      rw [hdiv, hmod, ih hw]

/-- Definition 11: accumulator form of the base-four encoding. -/
theorem encode_foldl (word : List ℕ) (start : ℕ) :
    word.foldl (fun h s => 4 * h + s) start = start * 4 ^ word.length + encode word := by
  induction word generalizing start with
  | nil => simp [encode]
  | cons symbol word ih =>
      simp only [List.foldl_cons, List.length_cons, encode, Nat.mul_zero, Nat.zero_add]
      rw [ih (4 * start + symbol), ih symbol]
      ring

/-- Definition 11: concatenating words concatenates their base-four digits. -/
theorem encode_append (left right : List ℕ) :
    encode (left ++ right) = encode left * 4 ^ right.length + encode right := by
  simp only [encode, List.foldl_append]
  exact encode_foldl right _

/-- Definition 11: a valid word fits within its fixed-length encoding range. -/
theorem encode_lt_pow {word : List ℕ} (hword : ∀ symbol ∈ word, symbol < 4) :
    encode word < 4 ^ word.length := by
  induction word using List.reverseRecOn with
  | nil => simp [encode]
  | append_singleton word symbol ih =>
      have hs : symbol < 4 := hword symbol (by simp)
      have hw : ∀ s ∈ word, s < 4 := fun s h => hword s (by simp [h])
      have hprev := ih hw
      rw [encode_append_singleton, List.length_append, List.length_singleton, pow_succ]
      omega

/-- Definition 11: reducing an input history modulo its storage range does
not change the next shifted history. -/
theorem destination_mod_input (history symbol : ℕ) {memory : ℕ} :
    destination (history % 4 ^ memory) symbol memory = destination history symbol memory := by
  simp [destination, Nat.add_mod, Nat.mul_mod]

/-- Definition 11: repeated shift-and-append is base-four accumulation modulo
the history range. This identity has no alphabet assumptions. -/
theorem foldl_destination_mod (word : List ℕ) (history : ℕ) {memory : ℕ} :
    word.foldl (destination (memory := memory)) (history % 4 ^ memory) =
      (word.foldl (fun h s => 4 * h + s) history) % 4 ^ memory := by
  induction word generalizing history with
  | nil => rfl
  | cons symbol word ih =>
      rw [List.foldl_cons, destination_mod_input]
      exact ih (4 * history + symbol)

/-- Definition 11: appending symbols to a valid-length encoded history is
encoding the concatenated word and retaining the prescribed number of symbols. -/
theorem foldl_destination (word : List ℕ) {history memory : ℕ}
    (hbound : history < 4 ^ memory) :
    word.foldl (destination (memory := memory)) history =
      (history * 4 ^ word.length + encode word) % 4 ^ memory := by
  have h := foldl_destination_mod word history (memory := memory)
  rw [Nat.mod_eq_of_lt hbound, encode_foldl] at h
  exact h

/-- Definition 11: reduction modulo a base-four power keeps exactly that
many final symbols. The length hypothesis excludes any zero-padding issue. -/
theorem encode_suffix {word : List ℕ} {length : ℕ}
    (hlength : length ≤ word.length) (hword : ∀ s ∈ word, s < 4) :
    encode word % 4 ^ length = encode (word.drop (word.length - length)) := by
  let skipped := word.length - length
  have hdrop : (word.drop skipped).length = length := by
    simp only [List.length_drop, skipped]
    omega
  have hsmall : encode (word.drop skipped) < 4 ^ length := by
    rw [← hdrop]
    exact encode_lt_pow (fun s hs => hword s (List.mem_of_mem_drop hs))
  change encode word % 4 ^ length = encode (word.drop skipped)
  conv_lhs => rw [← List.take_append_drop skipped word, encode_append]
  rw [hdrop]
  simpa [Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_of_lt hsmall

/-- Section 4.5, word update: a fold of `destination` consumes symbols and
keeps exactly the trailing history of the prescribed length. -/
theorem foldl_destination_encode {history word : List ℕ} {memory : ℕ}
    (hlength : history.length = memory)
    (hhistory : ∀ s ∈ history, s < 4) (hword : ∀ s ∈ word, s < 4) :
    word.foldl (destination (memory := memory)) (encode history) =
      encode ((history ++ word).drop word.length) := by
  have hbound : encode history < 4 ^ memory := by
    rw [← hlength]
    exact encode_lt_pow hhistory
  rw [foldl_destination word hbound, ← encode_append]
  have hvalid : ∀ s ∈ history ++ word, s < 4 := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hhistory s hs
    · exact hword s hs
  have hlen : memory ≤ (history ++ word).length := by simp [hlength]
  have h := encode_suffix hlen hvalid
  simpa [List.length_append, hlength] using h

/-- Section 4.3, an output edge: for any positive history length, append one
symbol and remove the oldest retained symbol. Corollary 19 uses length forty. -/
theorem destination_encode_of_pos {history : List ℕ} {symbol memory : ℕ}
    (hmemory : 0 < memory) (hlength : history.length = memory)
    (hhistory : ∀ s ∈ history, s < 4) (hsymbol : symbol < 4) :
    destination (encode history) symbol memory = encode (history.drop 1 ++ [symbol]) := by
  have h := foldl_destination_encode hlength hhistory
    (show ∀ s ∈ [symbol], s < 4 by simpa using hsymbol)
  simpa [List.drop_append_of_le_length (by omega : 1 ≤ history.length)] using h

/-- Section 4.3: the twelve-symbol specialization of `destination_encode_of_pos`,
used by the original verification of Proposition 17. -/
theorem destination_encode {history : List ℕ} {symbol : ℕ}
    (hlength : history.length = historyLength)
    (hhistory : ∀ s ∈ history, s < 4) (hsymbol : symbol < 4) :
    destination (encode history) symbol = encode (history.drop 1 ++ [symbol]) :=
  destination_encode_of_pos (by decide) hlength hhistory hsymbol

end Queens.Finite
