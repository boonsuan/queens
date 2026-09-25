import Queens.Finite.HistoryTable
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

/-!
# The local calculation

This file implements Definitions 9–11 and Algorithm 1 in Sections 4–5 of
*Greedy Queens and the Golden Ratio*. Histories are fixed-length base-four
numbers (twelve symbols by default, forty for Corollary 19); finite sets of
nonnegative offsets are bit masks. These representation
choices follow the independent bit-mask verifier supplied with the paper.

`calculate` is a total, branching computation. An absent history vertex, an
empty request, a failed output check, or exhausted row-search fuel produces an
explicit error. Thus successful verification cannot silently discard a branch.
The separate certificate file checks that none of these failures occurs on its
finite invariant. Relating these records to the infinite greedy board is the
separate mathematical content of Lemma 16.
-/

namespace Queens.Finite

/-- Section 4.3: the default number of retained symbols. The calculation also
accepts an explicit history length, as needed for Corollary 19. -/
def historyLength : ℕ := 12

/-- Definition 9: the upper-column bit of the symbol `2u + b`. -/
def upperBit (symbol : ℕ) : ℕ := symbol / 2

/-- Definition 9: the upper-row bit of the symbol `2u + b`. -/
def rowBit (symbol : ℕ) : ℕ := symbol % 2

/-- Definition 11: encode a word in base four, with its newest symbol last. -/
def encode (word : List ℕ) : ℕ := word.foldl (fun h s => 4 * h + s) 0

/-- Definition 11: decode a fixed-length base-four history, oldest symbol first. -/
def decode (code : ℕ) : ℕ → List ℕ
  | 0 => []
  | length + 1 => decode (code / 4) length ++ [code % 4]

/-- Definition 11: dropping the oldest symbol and appending a new symbol. -/
def destination (history symbol : ℕ) (memory : ℕ := historyLength) : ℕ :=
  (4 * history + symbol) % 4 ^ memory

/-- Section 4.2: test membership in a finite set represented by a bit mask. -/
def hasOffset (mask offset : ℕ) : Bool := (mask >>> offset) % 2 == 1

/-- Section 4.2: the finite set represented by an offset bit mask. Every set
bit has index below the mask itself; `mem_offsets` proves this representation exact. -/
def offsets (mask : ℕ) : Finset ℕ :=
  (Finset.range mask).filter (fun offset => hasOffset mask offset = true)

/-- Section 4.2: decoding a record preserves membership exactly. -/
@[simp] theorem mem_offsets {mask offset : ℕ} :
    offset ∈ offsets mask ↔ hasOffset mask offset = true := by
  simp only [offsets, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    have hpow : 2 ^ offset ≤ mask := by
      by_contra hn
      have hlt : mask < 2 ^ offset := by omega
      simp [hasOffset, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt] at h
    exact lt_of_lt_of_le (Nat.lt_pow_self (by omega : 1 < 2)) hpow

/-- Condition 15: a mask below 32 with zero low bit represents only offsets 1–4. -/
theorem offsets_subset_Icc {mask : ℕ} (hbound : mask < 32) (heven : mask % 2 = 0) :
    offsets mask ⊆ Finset.Icc 1 4 := by
  have hfinite : ∀ m : Fin 32, m.val % 2 = 0 → offsets m.val ⊆ Finset.Icc 1 4 := by
    decide
  exact hfinite ⟨mask, hbound⟩ heven

/-- Condition 15: each bounded row or diagonal record contains at most four offsets. -/
theorem offsets_card_le_four {mask : ℕ} (hbound : mask < 32) (heven : mask % 2 = 0) :
    (offsets mask).card ≤ 4 := by
  have h := Finset.card_le_card (offsets_subset_Icc hbound heven)
  norm_num at h ⊢
  exact h

/-- Section 4.5: insert an offset into a bit-mask record. -/
def insertOffset (mask offset : ℕ) : ℕ := mask ||| (1 <<< offset)

/-- Definition 10: the eight local records; `R`, `D`, and `A` are bit masks.
`input` and `output` encode the two histories and `queue` stores symbols oldest first. -/
structure State where
  /-- Definition 10: the lower-candidate width `n - m - d`. -/
  w : ℤ
  /-- Definition 10: displacement `n - m - U(m - 1)`. -/
  z : ℤ
  /-- Definition 10: retained lower-queen row offsets, measured from `m`. -/
  R : ℕ
  /-- Definition 10: retained lower-diagonal offsets, measured from `d`. -/
  D : ℕ
  /-- Definition 10: retained lower-antidiagonal offsets, measured from `n + m`. -/
  A : ℕ
  /-- Definition 10: the retained symbols immediately before `m`, encoded in base four. -/
  input : ℕ
  /-- Definition 10: already read symbols beginning at `m`, oldest first. -/
  queue : List ℕ
  /-- Definition 10: the retained symbols immediately before `n`, encoded in base four. -/
  output : ℕ
  deriving DecidableEq, BEq, Ord, Repr

/-- Definition 11: the labels allowed after an encoded input history. -/
def HistoryGraph.answers (graph : HistoryGraph) (vertex : ℕ) : Option (List ℕ) := do
  let mask ← graph.lookup vertex
  pure ((List.range 4).filter (hasOffset mask))

/-- Condition 15, in the bit-mask representation: the only permitted offsets
of `R` and `D` are 1, 2, 3, and 4. There is no lower bound on `w`. -/
def Condition (s : State) : Prop :=
  s.w ≤ 4 ∧ -4 ≤ s.z ∧ s.z ≤ 5 ∧
  s.R < 32 ∧ s.R % 2 = 0 ∧ s.D < 32 ∧ s.D % 2 = 0

/-- Condition 15 is decidable from its five numerical records. -/
instance (s : State) : Decidable (Condition s) := inferInstanceAs (Decidable (_ ∧ _))

/-- Condition 15, translated from the executable masks to ordinary finite sets. -/
theorem Condition.offsets_subset {s : State} (h : Condition s) :
    offsets s.R ⊆ Finset.Icc 1 4 ∧ offsets s.D ⊆ Finset.Icc 1 4 :=
  ⟨offsets_subset_Icc h.2.2.2.1 h.2.2.2.2.1,
    offsets_subset_Icc h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩

/-- Section 6.4: Condition 15 bounds the local lower-diagonal discrepancy.
Identifying this expression with `dⱼ - j` is the board rank identity of Section 4.1. -/
theorem Condition.discrepancy_bound {s : State} (h : Condition s)
    {r : ℕ} (hr : (r : ℤ) ≤ s.w) : |s.w - r - (offsets s.D).card| ≤ (4 : ℤ) := by
  have hw := h.1
  have hcard := offsets_card_le_four h.2.2.2.2.2.1 h.2.2.2.2.2.2
  rw [abs_le]
  constructor <;> omega

/-- Section 4.5: errors which invalidate the entire finite certificate. -/
inductive Failure where
  | missingInputVertex
  | emptyRequest
  | missingOutputEdge
  | invalidOutputBit
  | rowSearchExhausted
  deriving DecidableEq, Repr

/-- Algorithm 1: combine all branches, propagating any branch failure to the
whole calculation. The recursive definition exposes both branch obligations. -/
def allBranches {α β : Type} : List α →
    (α → Except Failure (List β)) → Except Failure (List β)
  | [], _ => .ok []
  | x :: xs, f => do
      let first ← f x
      let rest ← allBranches xs f
      return first ++ rest

/-- Algorithm 1, `Extend`: read exactly `extra` additional symbols, branching
over every allowed answer. No failure is converted into an empty successor list. -/
def extendBy (graph : HistoryGraph) (input extra : ℕ) (queue : List ℕ)
    (memory : ℕ := historyLength) : Except Failure (List (List ℕ)) :=
  match extra with
  | 0 => .ok [queue]
  | extra + 1 => do
      let vertex := queue.foldl (destination (memory := memory)) input
      let symbols ← match graph.answers vertex with
        | none => .error .missingInputVertex
        | some [] => .error .emptyRequest
        | some (s :: ss) => .ok (s :: ss)
      allBranches symbols fun symbol => extendBy graph input extra (queue ++ [symbol]) memory

/-- Algorithm 1, `Extend(k)`: a negative requested length requires no extension. -/
def extendQueue (graph : HistoryGraph) (input : ℕ) (queue : List ℕ)
    (length : ℤ) (memory : ℕ := historyLength) : Except Failure (List (List ℕ)) :=
  extendBy graph input (length.toNat - queue.length) queue memory

/-- Section 4.4: the retained upper sources before `m`, as `(h, Γ(h))`.
The count at position `i` is minus the upper-column bits strictly after it.
Writing this directly with a suffix sum makes the connection to `U` explicit. -/
def historyColumns (history : List ℕ) : List (ℤ × ℤ) :=
  history.zipIdx.filterMap fun (symbol, i) =>
    if upperBit symbol = 1 then
      some ((i : ℤ) - history.length,
        -(((history.drop (i + 1)).map upperBit).sum : ℤ))
    else none

/-- Section 4.4: the retained upper sources at or after `m`, as `(h, Γ(h))`.
The count includes the upper-column bit at `h`, hence the prefix of length `h+1`. -/
def queueColumns (queue : List ℕ) : List (ℤ × ℤ) :=
  queue.zipIdx.filterMap fun (symbol, i) =>
    if upperBit symbol = 1 then
      some ((i : ℤ), (((queue.take (i + 1)).map upperBit).sum : ℤ))
    else none

/-- Section 4.4: all retained upper sources, as the pairs `(h, Γ(h))` used in
Propositions 12–13. History sources precede queue sources, oldest first. -/
def upperColumns (s : State) (queue : List ℕ) (memory : ℕ := historyLength) :
    List (ℤ × ℤ) :=
  historyColumns (decode s.input memory) ++ queueColumns queue

/-- Proposition 12: the stored upper-antidiagonal attack test. -/
def antidiagonalAttack (s : State) (queue : List ℕ) (r : ℕ)
    (memory : ℕ := historyLength) : Bool :=
  (upperColumns s queue memory).any (fun (h, gamma) => 2 * h + gamma == s.z + r)

/-- Section 4.4 and Proposition 13: the row-count adjustment `J(x)`. -/
def adjustment (s : State) (queue : List ℕ) (x : ℤ)
    (memory : ℕ := historyLength) : ℤ :=
  (((upperColumns s queue memory).filter
    (fun (h, gamma) => decide (0 ≤ h ∧ h + gamma ≤ x))).length : ℤ) -
    (((upperColumns s queue memory).filter
      (fun (h, gamma) => decide (h < 0 ∧ x < h + gamma))).length : ℤ)

/-- Algorithm 1: a queen choice, where `none` denotes an upper queen. -/
abbrev Choice := Option ℕ × List ℕ

/-- Algorithm 1, the candidate loop: `remaining` is the number of candidates
still to test. All failures from queue extension invalidate the calculation. -/
def chooseFrom (graph : HistoryGraph) (s : State) (remaining r : ℕ) (queue : List ℕ)
    (memory : ℕ := historyLength) : Except Failure (List Choice) :=
  match remaining with
  | 0 => .ok [(none, queue)]
  | remaining + 1 => do
      if hasOffset s.R r || hasOffset s.D (s.w - r).toNat || hasOffset s.A r then
        chooseFrom graph s remaining (r + 1) queue memory
      else
        let queues ← extendQueue graph s.input queue (1 + max (r : ℤ) ((s.z + r) / 2)) memory
        allBranches queues fun q =>
          if rowBit (q[r]?.getD 0) = 0 ∧ !antidiagonalAttack s q r memory then
            .ok [(some r, q)]
          else chooseFrom graph s remaining (r + 1) q memory

/-- Algorithm 1, the row search. Fuel exhaustion is an error, so the finite
check certifies termination within this explicit bound rather than assuming it. -/
def findFreeRow (graph : HistoryGraph) (input rows fuel h : ℕ) (queue : List ℕ)
    (memory : ℕ := historyLength) : Except Failure (List (ℕ × List ℕ)) :=
  match fuel with
  | 0 => .error .rowSearchExhausted
  | fuel + 1 => do
      let queues ← extendQueue graph input queue (h + 1) memory
      allBranches queues fun q =>
        if !hasOffset rows h ∧ rowBit (q[h]?.getD 0) = 0 then
          .ok [(h, q)]
        else findFreeRow graph input rows fuel (h + 1) q memory

/-- Section 4.5: the least absent offset in a bit-mask diagonal record.
Searching through `mask + 1` is always enough, including for the empty record. -/
def diagonalAdvance (mask : ℕ) : ℕ :=
  ((List.range (mask + 1)).find? (fun h => !hasOffset mask h)).getD (mask + 1)

/-- Equation (update), Section 4.5: construct the successor after inserting a
choice and finding the reference advances. `queue` includes all symbols read by
the row search; `mu` of them are consumed by the new input reference. -/
def updateState (s : State) (rows diagonals antidiagonals nu mu : ℕ)
    (queue : List ℕ) (symbol : ℕ) (memory : ℕ := historyLength) : State :=
  let consumed := queue.take mu
  { w := s.w + 1 - mu - nu
    z := s.z + 1 - mu - (consumed.map upperBit).sum
    R := rows >>> mu
    D := diagonals >>> nu
    A := antidiagonals >>> (1 + mu)
    input := consumed.foldl (destination (memory := memory)) s.input
    queue := queue.drop mu
    output := destination s.output symbol memory }

/-- Algorithm 1: finish one queen choice, check its output, and perform every
branch of the row search and record update. -/
def finishChoice (graph : HistoryGraph) (s : State) (choice : Choice)
    (memory : ℕ := historyLength) :
    Except Failure (List State) := do
  let (r, queue) := choice
  let bit := adjustment s queue s.z memory - adjustment s queue (s.z - 1) memory
  if bit < 0 ∨ 1 < bit then throw .invalidOutputBit
  let symbol := (if r.isSome then 0 else 2) + bit.toNat
  match graph.lookup s.output with
  | none => throw .missingOutputEdge
  | some mask => if !hasOffset mask symbol then throw .missingOutputEdge
  let rows := r.elim s.R (insertOffset s.R)
  let diagonals := r.elim s.D (fun h => insertOffset s.D (s.w - h).toNat)
  let antidiagonals := r.elim s.A (insertOffset s.A)
  let nu := diagonalAdvance diagonals
  let advances ← findFreeRow graph s.input rows 8 0 queue memory
  return advances.map fun (mu, q) =>
    updateState s rows diagonals antidiagonals nu mu q symbol memory

/-- Algorithm 1 of Section 4.5: the complete set of branches, with multiplicity.
An error in any branch is an error for the entire calculation. The row-search
bound of eight is checked computationally, and never used to drop a branch. -/
def calculate (graph : HistoryGraph) (s : State) (memory : ℕ := historyLength) :
    Except Failure (List State) := do
  let queues ← extendQueue graph s.input s.queue s.z memory
  let choices ← allBranches queues fun q => chooseFrom graph s (s.w + 1).toNat 0 q memory
  allBranches choices (finishChoice graph s (memory := memory))

/-- Section 6.1: the local state before column 30, transcribed from the table.
Its identification with the greedy board is proved by `initialState_represented`
in `Queens.Finite.Seed`. -/
def initialState : State :=
  { w := 0, z := -1, R := 0, D := 2, A := 0
    input := encode [2, 3, 0, 1, 2, 1, 2, 1, 2, 2, 2, 3]
    queue := [0, 0, 3, 2, 2, 3, 0, 1, 2, 1, 2]
    output := encode [3, 0, 0, 3, 2, 2, 3, 0, 1, 2, 1, 2] }

/-- Section 6.1: the displayed starting record satisfies Condition 15. -/
theorem initialState_condition : Condition initialState := by decide

end Queens.Finite
