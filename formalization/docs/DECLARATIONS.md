# Declaration index

Generated from the source docstrings by `python3 scripts/declaration_index.py`.
The README maps modules to numbered paper results; the descriptions below
record each named definition or result's role. Private helpers, instances,
structure fields, and generated auxiliary declarations are omitted.

## `Queens/Counting.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`counting_recurrence_int`](../Queens/Counting.lean#L17) | Lemma 7 in integer arithmetic. A column estimate at consecutive lower columns bounds the recurrence defect. Keeping the calculation in `ℤ` retains the one-unit improvement of a strict integer endpoint bound. |
| [`counting_recurrence`](../Queens/Counting.lean#L51) | The real-valued formulation of Lemma 7, directly usable by `count_error_lt`. All combinatorial assumptions remain explicit. |

## `Queens/DiagonalCoverage.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`upperCount_unbounded`](../Queens/DiagonalCoverage.lean#L19) | The upper count is unbounded, as used in Corollary 18. The proved golden-ratio estimate supplies an upper rank beyond any prescribed bound. |
| [`exists_upper_diagonal`](../Queens/DiagonalCoverage.lean#L37) | Every positive upper diagonal is occupied. Lemma 2 identifies upper diagonals with upper ranks, and the upper count reaches every such rank. |
| [`exists_lower_diagonal`](../Queens/DiagonalCoverage.lean#L47) | Every positive lower-diagonal magnitude is occupied. The finite invariant keeps at most four used magnitudes above the least unused magnitude; hence the reference eventually passes every fixed positive magnitude (Corollary 18). |
| [`q_diagonal_surjective`](../Queens/DiagonalCoverage.lean#L71) | **Corollary 18, coverage.** Every integer occurs as the signed diagonal `q n - n` of some greedy queen. Zero is occupied by the queen at the origin. |
| [`q_diagonal_bijective`](../Queens/DiagonalCoverage.lean#L88) | **Corollary 18 (diagonal coverage).** The signed-diagonal map is a bijection from natural column indices to all integers. |
| [`existsUnique_queen_on_diagonal`](../Queens/DiagonalCoverage.lean#L93) | **Corollary 18**, expressed geometrically: every signed diagonal contains exactly one queen of the greedy construction. |
| [`lowerDiagonal_injective`](../Queens/DiagonalCoverage.lean#L98) | Chronological lower queens have distinct positive diagonal magnitudes, the injectivity part of Corollary 18's final assertion. |
| [`lowerDiagonal_bijOn`](../Queens/DiagonalCoverage.lean#L111) | **Corollary 18, lower diagonals.** The chronological lower magnitudes enumerate the positive integers bijectively. |

## `Queens/ErrorRecursion.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`leastUnused_le_card`](../Queens/ErrorRecursion.lean#L23) | A finite set's least unused natural number is at most its cardinality. This counting fact bounds the row reference in the proof of Lemma 20. |
| [`rowReference_le`](../Queens/ErrorRecursion.lean#L31) | There is an unused row among `0, …, n` before column `n`. This is the reference bound used in Section 6, Lemma 20. |
| [`rowReference_isLowerRow`](../Queens/ErrorRecursion.lean#L38) | The least unused row after the origin is a lower row: an upper queen in that row would already have been placed. This is the first rank argument in Section 6, Lemma 20. |
| [`referenceLowerRank`](../Queens/ErrorRecursion.lean#L52) | The number `t` of lower rows strictly below the current least unused row, as introduced in Section 6, Lemma 20. This counts all lower rows, not just those known to be occupied before the current column. |
| [`sortedLowerRow_referenceLowerRank`](../Queens/ErrorRecursion.lean#L58) | The least unused row has zero-based rank `referenceLowerRank n` among the lower rows, by the rank characterization used in Lemma 20. |
| [`rowReference_eq_rank_add_count`](../Queens/ErrorRecursion.lean#L65) | The row reference identity `m = t + 1 + U(t)` from Section 6, Lemma 20, obtained by applying Lemma 4 to the first unused lower row. |
| [`earlierLowerColumns_card`](../Queens/ErrorRecursion.lean#L71) | The lower queens strictly before column `n` are counted by `L(n - 1)`. This connects the local records with the global count in Lemma 20. |
| [`rowOffsets_card`](../Queens/ErrorRecursion.lean#L80) | Offsetting the retained lower rows does not change their count. This interprets `\|R\|` in the rank identity of Section 6, Lemma 20. |
| [`referenceLowerRank_eq_card`](../Queens/ErrorRecursion.lean#L92) | All lower rows below the least unused row have already been occupied. This finite counting identity is the key interpretation of `t` in Lemma 20. |
| [`referenceLowerRank_add_card_rowOffsets`](../Queens/ErrorRecursion.lean#L116) | The lower rows already used split at the least unused row into `t` rows below it and the `\|R\|` retained rows above it: `t + \|R\| = L(n - 1)`. This is the second rank identity in Section 6, Lemma 20. |
| [`referenceLowerRank_lt`](../Queens/ErrorRecursion.lean#L126) | The recursive argument in Lemma 20 is strictly earlier than `n - 1` once column one, an upper column, has been filled. |
| [`upperCount_eq_reference_window`](../Queens/ErrorRecursion.lean#L136) | The local diagonal rank identity gives `U(n - 1) = m + w - \|D\|`, the first counting equation in Section 6, Lemma 20. Signed arithmetic avoids truncated subtraction when the window is negative. |
| [`exact_error_recursion`](../Queens/ErrorRecursion.lean#L149) | **Lemma 20 (exact error recursion).** The upper-count error before column `n` is a contracting affine function of the error at the lower-row rank of its least unused row. This holds already for every positive column; `referenceLowerRank_lt` supplies the strict decrease needed in Proposition 21. |

## `Queens/Exactness.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`local_step_exact`](../Queens/Exactness.lean#L18) | **Lemma 16 (the records determine the actual step)**, in the exact form needed by the induction of Section 6.4. The preliminary extension, candidate choice, and finishing traversal each retain the actual branch. |
| [`bounded_diagonal_discrepancy`](../Queens/Exactness.lean#L27) | **Lemma 5 (bounded diagonal discrepancy).** The chronological lower diagonal of positive rank `k + 1` differs from that rank by at most four. |
| [`main`](../Queens/Exactness.lean#L33) | **Theorem 1.** The actual greedy queens lie within the paper's stated strict bounds of the two golden-ratio lines. The statement also covers `n = 0`, where both implications have false antecedents. |

## `Queens/Finite/Branching.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`allBranches_branch`](../Queens/Finite/Branching.lean#L18) | If a branching traversal succeeds, each visited input has a successful result, and every result of that input belongs to the combined output. This is the no-dropped-branches property used in Lemma 16. |
| [`PermittedPath`](../Queens/Finite/Branching.lean#L42) | Definition 11: a finite list of permitted labels starting at a specified encoded history. The memory parameter also covers the forty-symbol graph used in Corollary 19. This is a local path, without an assumption about the board. |
| [`extendBy_contains_path`](../Queens/Finite/Branching.lean#L53) | A successful `Extend` retains any prescribed permitted suffix of the requested length. This is the operational input-path part of Lemma 16. |
| [`calculate_decompose`](../Queens/Finite/Branching.lean#L83) | A successful complete calculation has successful preliminary extension, candidate traversal, and finishing traversal. This exposes the three stages of Algorithm 1 for the semantic correspondence proof. |

## `Queens/Finite/Certificate.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`initialState_certified`](../Queens/Finite/Certificate.lean#L18) | Section 6.1: the displayed starting state is included in the checked table. |
| [`certified_condition`](../Queens/Finite/Certificate.lean#L22) | Proposition 17: each certified state satisfies Condition 15. |
| [`certified_successors`](../Queens/Finite/Certificate.lean#L30) | Proposition 17: every branch succeeds and returns another certified state. The existential records successful termination of the total calculation, so this statement cannot be satisfied by discarding an unsuccessful branch. |
| [`Step`](../Queens/Finite/Certificate.lean#L45) | Definition 14: one edge of the calculated local-state graph. |
| [`certified_step`](../Queens/Finite/Certificate.lean#L49) | Definition 14: every edge leaving a certified state stays in the certificate. |
| [`reachable_certified`](../Queens/Finite/Certificate.lean#L59) | Section 6.4, the finite-state part of the induction: any finite walk of the local calculation from the starting record stays in the certificate. |
| [`reachable_condition`](../Queens/Finite/Certificate.lean#L68) | Section 6.4: every locally reachable record satisfies Condition 15. The additional assertion that the actual greedy board traces such a walk is exactly the separate semantic bridge in Lemma 16. |
| [`states_size`](../Queens/Finite/Certificate.lean#L76) | Proposition 17: the checked invariant table contains 7014 entries. Together with `states_nodup`, this counts distinct states. |
| [`stateIndex_lookup_checked`](../Queens/Finite/Certificate.lean#L82) | Proposition 17: every state entry recovers its own index by lookup. This kernel check supplies both uniqueness and auxiliary witness identification. |
| [`states_nodup`](../Queens/Finite/Certificate.lean#L93) | Proposition 17: the 7014 entries in the checked invariant are distinct. |

## `Queens/Finite/CertificateChunks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`certificate_checked`](../Queens/Finite/CertificateChunks.lean#L800) | Proposition 17: every state in the candidate invariant satisfies the independently recomputed check. Each bounded check is verified by Lean's kernel; the final assembly covers every state in the original table. |

## `Queens/Finite/CertificateCore.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`Certified`](../Queens/Finite/CertificateCore.lean#L18) | Proposition 17: a state is certified when it occurs in the generated table. |
| [`stateIndex_entries`](../Queens/Finite/CertificateCore.lean#L23) | Proposition 17: the generated search layout contains exactly the invariant states in their original order, by projecting the checked indexed alignment. |
| [`certified_of_lookupState`](../Queens/Finite/CertificateCore.lean#L30) | Proposition 17: successful lookup in the proposed balanced state index gives genuine membership in the invariant. Its layout is not a trusted input. |
| [`checkState`](../Queens/Finite/CertificateCore.lean#L44) | Proposition 17: check Condition 15 and recompute every branch, checking that each successor belongs to the same finite invariant. |

## `Queens/Finite/Data.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`historyGraph`](../Queens/Finite/Data.lean#L158) | Definition 11 and Section 6.2: the supplied twelve-symbol history graph, stored in a balanced tree for kernel evaluation. |
| [`stateIndex`](../Queens/Finite/Data.lean#L7890) | Proposition 17: the proposed balanced state index; its agreement with the invariant table is checked in Lean. |
| [`stateChunks`](../Queens/Finite/Data.lean#L7894) | Proposition 17: bounded chunks of the candidate invariant, allowing separate kernel checks. |
| [`states`](../Queens/Finite/Data.lean#L7898) | Proposition 17: the candidate closed invariant, sorted by all eight fields. |

## `Queens/Finite/Encoding.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`decode_length`](../Queens/Finite/Encoding.lean#L15) | Definition 11: decoding always produces the specified number of symbols. |
| [`encode_append_singleton`](../Queens/Finite/Encoding.lean#L21) | Definition 11: appending one symbol is one base-four accumulation step. |
| [`decode_encode`](../Queens/Finite/Encoding.lean#L27) | Definition 11: the base-four encoding and fixed-length decoding are inverse on words over the paper's alphabet `{0,1,2,3}`. |
| [`encode_foldl`](../Queens/Finite/Encoding.lean#L40) | Definition 11: accumulator form of the base-four encoding. |
| [`encode_append`](../Queens/Finite/Encoding.lean#L50) | Definition 11: concatenating words concatenates their base-four digits. |
| [`encode_lt_pow`](../Queens/Finite/Encoding.lean#L56) | Definition 11: a valid word fits within its fixed-length encoding range. |
| [`destination_mod_input`](../Queens/Finite/Encoding.lean#L69) | Definition 11: reducing an input history modulo its storage range does not change the next shifted history. |
| [`foldl_destination_mod`](../Queens/Finite/Encoding.lean#L75) | Definition 11: repeated shift-and-append is base-four accumulation modulo the history range. This identity has no alphabet assumptions. |
| [`foldl_destination`](../Queens/Finite/Encoding.lean#L86) | Definition 11: appending symbols to a valid-length encoded history is encoding the concatenated word and retaining the prescribed number of symbols. |
| [`encode_suffix`](../Queens/Finite/Encoding.lean#L96) | Definition 11: reduction modulo a base-four power keeps exactly that many final symbols. The length hypothesis excludes any zero-padding issue. |
| [`foldl_destination_encode`](../Queens/Finite/Encoding.lean#L113) | Section 4.5, word update: a fold of `destination` consumes symbols and keeps exactly the trailing history of the prescribed length. |
| [`destination_encode_of_pos`](../Queens/Finite/Encoding.lean#L133) | Section 4.3, an output edge: for any positive history length, append one symbol and remove the oldest retained symbol. Corollary 19 uses length forty. |
| [`destination_encode`](../Queens/Finite/Encoding.lean#L143) | Section 4.3: the twelve-symbol specialization of `destination_encode_of_pos`, used by the original verification of Proposition 17. |

## `Queens/Finite/FinishSemantics.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`HistoryGraph.answer_contains`](../Queens/Finite/FinishSemantics.lean#L16) | An allowed four-symbol label occurs in the graph's answer list. |
| [`HistoryGraph.followsThrough_succ`](../Queens/Finite/FinishSemantics.lean#L23) | A checked next-symbol edge extends the actual word's verified graph path. |
| [`choice_symbol_eq`](../Queens/Finite/FinishSemantics.lean#L48) | The symbol formed from the actual upper/lower choice and the actual row bit is exactly Definition 9's queen-word symbol. |
| [`finishChoice_contains_actual_of_extensions_general`](../Queens/Finite/FinishSemantics.lean#L64) | A successful finish of the actual queen choice contains the actual next state and extends the verified queen-word path. This is the final operational part of Section 5, Lemma 16, generalized to any memory of at least twelve symbols for the forty-symbol construction of Corollary 19. The geometric count bound remains twelve, independently of the larger memory. |
| [`finishChoice_contains_actual_of_extensions`](../Queens/Finite/FinishSemantics.lean#L171) | The finishing stage specialized to twelve-symbol histories after column 30. This wrapper supplies the numerical starting bounds used in Lemma 16. |
| [`finishChoice_contains_actual`](../Queens/Finite/FinishSemantics.lean#L187) | The actual finish stage for the paper's checked history graph. Its well-formedness and the actual-word extension hypothesis have both been proved. |

## `Queens/Finite/FortyCertificate.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`checkVertex`](../Queens/Finite/FortyCertificate.lean#L30) | Corollary 19: check record bounds, every index, and exact equality of the proposed and calculated successor sets. Failure of any branch rejects the vertex. |
| [`data_sizes`](../Queens/Finite/FortyCertificate.lean#L39) | Corollary 19: the finite data have exactly the reported numbers of history vertices, history edges, state-table entries, and indexed state edges. |
| [`historyGraph_wellFormed`](../Queens/Finite/FortyCertificate.lean#L51) | Corollary 19: the proposed forty-symbol history graph is well formed; every allowed output edge has a listed destination. |
| [`initialState_eq_state_zero`](../Queens/Finite/FortyCertificate.lean#L75) | The tree check applies to the canonical payload of every public vertex. -/ private theorem vertex_checked (v : Vertex) : checkVertexEntry (v.val, state v, successorIndices v) = true := by obtain ⟨payload, hmem, hstate, hedges⟩ := entry_at_vertex v have h := indexedAll_eq_true.mp vertexTable_checked (v.val, payload) hmem have hp : payload = (state v, successorIndices v) := Prod.ext hstate hedges rw [hp] at h exact h /-- Every listed target resolves in the canonical table. -/ private theorem successor_lookup {v : Vertex} {j : ℕ} (hj : j ∈ successorIndices v) : ∃ payload, indexedLookup j FortyData.vertexTable = some payload := by have h := vertex_checked v simp only [checkVertexEntry, Bool.and_eq_true_iff] at h have hj' := List.all_eq_true.mp h.1.2 j hj cases heq : indexedLookup j FortyData.vertexTable with \| none => simp only [heq, Option.isSome_none, Bool.false_eq_true] at hj' \| some payload => exact ⟨payload, rfl⟩ /-- Corollary 19: the seed before column 80 is vertex zero. |
| [`state_condition`](../Queens/Finite/FortyCertificate.lean#L84) | Corollary 19: an indexed graph state satisfies Condition 15. |
| [`successorIndex_lt`](../Queens/Finite/FortyCertificate.lean#L90) | Corollary 19: every proposed successor index is in range. |
| [`mem_successorStates_iff`](../Queens/Finite/FortyCertificate.lean#L111) | The balanced lookup and the public indexed graph have the same targets. -/ private theorem mem_fastSuccessorStates_vertex_iff {v : Vertex} {t : State} : t ∈ fastSuccessorStates (successorIndices v) ↔ ∃ w : Vertex, w.val ∈ successorIndices v ∧ state w = t := by rw [mem_fastSuccessorStates_iff] constructor · rintro ⟨j, hj, payload, hlookup, hstate⟩ obtain ⟨hjbound, heq⟩ := lookup_state_eq hlookup exact ⟨⟨j, hjbound⟩, hj, heq.trans hstate⟩ · rintro ⟨w, hw, heq⟩ obtain ⟨payload, hlookup⟩ := successor_lookup hw obtain ⟨hwbound, hstate⟩ := lookup_state_eq hlookup exact ⟨w.val, hw, payload, hlookup, hstate.symm.trans heq⟩ /-- Corollary 19: successful indexed adjacency identifies exactly the states in the proposed successor list, including a valid index witness. |
| [`calculated_successors`](../Queens/Finite/FortyCertificate.lean#L155) | The result component of both successor-set checkers. Keeping this small function abstract avoids expanding the generated graph in its soundness proof. -/ private def checkResult (result : Except Failure (List State)) (expected : List State) : Bool := match result with \| .error _ => false \| .ok next => decide (next.toFinset = expected.toFinset) /-- Decode the result component before specializing it to the generated graph. -/ private theorem checked_result_success {result : Except Failure (List State)} {expected : List State} (h : checkResult result expected = true) : ∃ next, result = .ok next ∧ next.toFinset = expected.toFinset := by cases result with \| error failure => exact Bool.noConfusion h \| ok next => exact ⟨next, rfl, of_decide_eq_true h⟩ /-- A successful calculation with the prescribed successor set passes the result component of the original array-based checker. -/ private theorem checked_result_of_eq {result : Except Failure (List State)} {next expected : List State} (hresult : result = .ok next) (hset : next.toFinset = expected.toFinset) : checkResult result expected = true := by rw [hresult] exact decide_eq_true hset /-- Corollary 19: all branches terminate, and their successor states are exactly the indexed outgoing edges. This is the interface used to lift the actual board to an indexed path before contracting runs and gaps. |
| [`certificate_checked`](../Queens/Finite/FortyCertificate.lean#L170) | Corollary 19: every public vertex passes the complete local calculation, with exactly the proposed adjacency set. This follows from the bounded kernel checks through the proved table-index correspondence. |
| [`Certified`](../Queens/Finite/FortyCertificate.lean#L184) | Corollary 19: table membership is the finite invariant underlying the forty-symbol verification. |
| [`initialState_certified`](../Queens/Finite/FortyCertificate.lean#L187) | Corollary 19: the actual-prefix starting record belongs to the invariant. |
| [`certified_condition`](../Queens/Finite/FortyCertificate.lean#L191) | Corollary 19: every state in the finite invariant satisfies Condition 15. |
| [`certified_successors`](../Queens/Finite/FortyCertificate.lean#L197) | Corollary 19: every calculated successor of a certified state is certified, and every branch of its calculation succeeds. |

## `Queens/Finite/FortyData.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`historyGraph`](../Queens/Finite/FortyData.lean#L1504) | Corollary 19: the balanced candidate forty-symbol history graph. |
| [`vertexTable`](../Queens/Finite/FortyData.lean#L3044) | Corollary 19: the canonical balanced table of indices, states, and outgoing indices. |
| [`states`](../Queens/Finite/FortyData.lean#L3048) | Corollary 19: candidate states in reference order, with the column-80 seed at index zero. |
| [`successors`](../Queens/Finite/FortyData.lean#L3052) | Corollary 19: candidate adjacency, projected from the same canonical table. |
| [`initialState`](../Queens/Finite/FortyData.lean#L3056) | Corollary 19: the proposed actual local state immediately before column 80. |

## `Queens/Finite/FortyHistoryChecks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`historyGraph_checked`](../Queens/Finite/FortyHistoryChecks.lean#L8890) | Corollary 19: kernel verification of the complete forty-symbol history graph, assembled from independently checked bounded subtrees. |

## `Queens/Finite/FortySeed.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`seedRows`](../Queens/Finite/FortySeed.lean#L22) | Corollary 19: the first eighty proposed rows, taken from the reproducible witness data and checked independently of the longer attainment prefix. |
| [`seedRow`](../Queens/Finite/FortySeed.lean#L25) | Corollary 19: the proposed row in the eighty-column starting prefix. |
| [`seedRows_checked`](../Queens/Finite/FortySeed.lean#L29) | Corollary 19: kernel verification of precisely the eighty-column seed, using the proved bitboard implementation of the defining greedy rule. |
| [`q_eq_seedRow`](../Queens/Finite/FortySeed.lean#L35) | Corollary 19: the eighty-column starting prefix agrees with the actual sequence, by the checked defining greedy rule. |
| [`seedSymbol`](../Queens/Finite/FortySeed.lean#L42) | Definition 9 evaluated on the first eighty columns, independently of the local calculation. |
| [`queenSymbol_eq_seedSymbol`](../Queens/Finite/FortySeed.lean#L47) | Corollary 19, Section 6.5: the computed finite queen word is the actual queen word. |
| [`occupiedRows_seed`](../Queens/Finite/FortySeed.lean#L52) | Corollary 19, Section 6.5: occupied rows obtained directly from the checked prefix. |
| [`earlierLowerColumns_seed`](../Queens/Finite/FortySeed.lean#L56) | Corollary 19, Section 6.5: the lower columns obtained directly from the checked prefix. |
| [`lowerDiagonals_seed`](../Queens/Finite/FortySeed.lean#L61) | Corollary 19, Section 6.5: used lower diagonals obtained directly from the checked prefix. |
| [`rowReference_eighty`](../Queens/Finite/FortySeed.lean#L66) | Corollary 19, Section 6.5: the actual least unused row before column 80 is 51. |
| [`diagonalReference_eighty`](../Queens/Finite/FortySeed.lean#L76) | Corollary 19, Section 6.5: the actual least unused positive lower diagonal is 32. |
| [`countReference_eighty`](../Queens/Finite/FortySeed.lean#L88) | Corollary 19, Section 6.5: the actual upper-count reference before column 80 is 31. |
| [`window_eighty`](../Queens/Finite/FortySeed.lean#L96) | Corollary 19, Section 6.5: the actual window record is the displayed initial value. |
| [`upperDisplacement_eighty`](../Queens/Finite/FortySeed.lean#L100) | Corollary 19, Section 6.5: the actual upper displacement is the displayed initial value. |
| [`rowOffsets_eighty`](../Queens/Finite/FortySeed.lean#L104) | Corollary 19, Section 6.5: the actual row record before column 80 is empty. |
| [`diagonalOffsets_eighty`](../Queens/Finite/FortySeed.lean#L110) | Corollary 19, Section 6.5: the actual diagonal record before column 80 is empty. |
| [`antidiagonalOffsets_eighty`](../Queens/Finite/FortySeed.lean#L116) | Corollary 19, Section 6.5: the actual antidiagonal record before column 80 is empty. |
| [`seedSegment`](../Queens/Finite/FortySeed.lean#L122) | Corollary 19, Section 6.5: a word segment computed from the finite seed table. |
| [`wordSegment_eq_seedSegment`](../Queens/Finite/FortySeed.lean#L127) | Corollary 19, Section 6.5: finite seed segments are actual queen-word segments whenever all their indices belong to the verified eighty-column prefix. |
| [`initialState_represented`](../Queens/Finite/FortySeed.lean#L136) | Corollary 19, Section 6.5: all eight displayed records, including the three word fields, represent the actual board before column 80. |
| [`seedWord_follows`](../Queens/Finite/FortySeed.lean#L158) | Corollary 19, Section 6.5: the seed word follows the checked history graph. |
| [`queenWord_follows_through_seventyNine`](../Queens/Finite/FortySeed.lean#L163) | Corollary 19, Section 6.5: the actual queen word through column 79 follows the graph, so the initial input and output histories are grounded in the greedy board. |

## `Queens/Finite/FortyStateChecks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`vertexTable_checked`](../Queens/Finite/FortyStateChecks.lean#L39) | Corollary 19: kernel verification of every state and every outgoing branch. Four independent quarter proofs and all three intervening nodes cover the complete tree; each finite check is reduced by the kernel. |

## `Queens/Finite/FortyStateChecksPart0.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`vertexQuarter0_checked`](../Queens/Finite/FortyStateChecksPart0.lean#L1683) | Corollary 19: kernel verification of quarter 1 of the forty-symbol state table, including every outgoing branch. |

## `Queens/Finite/FortyStateChecksPart1.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`vertexQuarter1_checked`](../Queens/Finite/FortyStateChecksPart1.lean#L1683) | Corollary 19: kernel verification of quarter 2 of the forty-symbol state table, including every outgoing branch. |

## `Queens/Finite/FortyStateChecksPart2.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`vertexQuarter2_checked`](../Queens/Finite/FortyStateChecksPart2.lean#L1683) | Corollary 19: kernel verification of quarter 3 of the forty-symbol state table, including every outgoing branch. |

## `Queens/Finite/FortyStateChecksPart3.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`vertexQuarter3_checked`](../Queens/Finite/FortyStateChecksPart3.lean#L1683) | Corollary 19: kernel verification of quarter 4 of the forty-symbol state table, including every outgoing branch. |

## `Queens/Finite/FortyTable.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`Vertex`](../Queens/Finite/FortyTable.lean#L19) | Corollary 19: indices of the proposed forty-symbol state table. |
| [`state`](../Queens/Finite/FortyTable.lean#L22) | Corollary 19: the state at an indexed graph vertex. |
| [`successorIndices`](../Queens/Finite/FortyTable.lean#L25) | Corollary 19: the proposed successor indices of a graph vertex. |
| [`successorStates`](../Queens/Finite/FortyTable.lean#L28) | Corollary 19: the successor states selected by the proposed adjacency. |
| [`vertexKeys_checked`](../Queens/Finite/FortyTable.lean#L35) | Corollary 19: the stored keys enumerate precisely the positions of the canonical table. Only natural-number keys are evaluated by this kernel check. |
| [`entry_state_get?`](../Queens/Finite/FortyTable.lean#L41) | A canonical entry identifies its state in the public array. |
| [`entry_successors_get?`](../Queens/Finite/FortyTable.lean#L48) | A canonical entry identifies its adjacency in the public array. |
| [`entry_index_lt`](../Queens/Finite/FortyTable.lean#L55) | A listed key is a valid index of the public state array. |
| [`entry_at_vertex`](../Queens/Finite/FortyTable.lean#L63) | Every public vertex has a corresponding canonical payload, with both its state and its adjacency identified. No lookup completeness is assumed. |
| [`fastSuccessorStates`](../Queens/Finite/FortyTable.lean#L81) | Corollary 19: read target states through the balanced table. Missing indices are discarded here but explicitly rejected by `checkVertexEntry`. |
| [`checkVertexEntry`](../Queens/Finite/FortyTable.lean#L87) | Corollary 19: check a state and its outgoing index list directly from the canonical tree. Every index must resolve, and the resulting successor set must agree exactly with all branches of the local calculation. |
| [`lookup_state_eq`](../Queens/Finite/FortyTable.lean#L96) | Corollary 19: a successful target lookup is the state at that exact public index. The statement uses only lookup soundness and the checked key alignment. |
| [`mem_fastSuccessorStates_iff`](../Queens/Finite/FortyTable.lean#L107) | The fast successor list has exactly the states returned by successful lookups of the listed target indices. |

## `Queens/Finite/GreedyPrefix.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`AttackBoard`](../Queens/Finite/GreedyPrefix.lean#L17) | Corollary 19, attainment checks: the attacked rows in the current column, separated into horizontal, upward-diagonal, and downward-diagonal attacks. |
| [`AttackBoard.empty`](../Queens/Finite/GreedyPrefix.lean#L27) | Rows already occupied by an earlier queen. -/ rows : ℕ /-- Attacks whose row increases when the column increases. -/ rising : ℕ /-- Attacks whose row decreases when the column increases. -/ falling : ℕ deriving DecidableEq /-- Corollary 19: the initially empty bitboard, before the queen at the origin. |
| [`AttackBoard.advance`](../Queens/Finite/GreedyPrefix.lean#L30) | Corollary 19: place a queen and advance to the next column. |
| [`AttackBoard.attacks`](../Queens/Finite/GreedyPrefix.lean#L35) | Corollary 19: the union of the three attack masks. |
| [`AttackBoard.checkRow`](../Queens/Finite/GreedyPrefix.lean#L39) | Corollary 19: a proposed queen is unattacked and all smaller rows are attacked. The bit-mask equality checks every smaller row simultaneously. |
| [`AttackBoard.checkRows`](../Queens/Finite/GreedyPrefix.lean#L43) | Corollary 19: verify every entry of a proposed prefix by the greedy rule. |
| [`AttackBoard.Represents`](../Queens/Finite/GreedyPrefix.lean#L49) | Corollary 19: a bitboard represents precisely the attacks of the actual queens strictly before column `n`. |
| [`AttackBoard.empty_represents`](../Queens/Finite/GreedyPrefix.lean#L55) | For Corollary 19, the empty board represents the defining greedy process before column zero. |
| [`AttackBoard.Represents.advance`](../Queens/Finite/GreedyPrefix.lean#L60) | For Corollary 19, advancing a represented attack board with the actual queen preserves its interpretation. This justifies the shifts in the finite prefix checker. |
| [`AttackBoard.Represents.available_iff`](../Queens/Finite/GreedyPrefix.lean#L112) | For Corollary 19, on a represented board, a clear bit is exactly an available row in the original least-unattacked-row definition. |
| [`AttackBoard.Represents.eq_q_of_checkRow`](../Queens/Finite/GreedyPrefix.lean#L131) | For Corollary 19, a successfully checked row on a represented board is the actual greedy choice, not just a legal nonattacking placement. |
| [`AttackBoard.Represents.q_eq_of_checkRows`](../Queens/Finite/GreedyPrefix.lean#L148) | For Corollary 19, every entry of a successfully checked list agrees with the actual greedy sequence, beginning at the column represented by its initial attack board. |

## `Queens/Finite/History.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`historyGraph_wellFormed`](../Queens/Finite/History.lean#L23) | Proposition 17: the supplied graph has no duplicate or malformed vertices, and every allowed transition stays inside it. The balanced-table checker reduces to an ordinary proof checked by the Lean kernel. |
| [`historyGraph_vertex_count`](../Queens/Finite/History.lean#L29) | Section 6.2 and Proposition 17: the graph contains 2092 vertices. |
| [`historyGraph_edge_count`](../Queens/Finite/History.lean#L35) | Section 6.2 and Proposition 17: the graph contains 2603 labeled edges. |
| [`historyGraph_no_dead_ends`](../Queens/Finite/History.lean#L42) | Proposition 17: every listed vertex has an outgoing edge, so requests at a graph vertex never terminate for lack of an answer. |

## `Queens/Finite/HistoryChecking.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`HistoryGraph.WellFormed`](../Queens/Finite/HistoryChecking.lean#L17) | Definition 11: a well-formed finite presentation has unique vertices, valid base-four and edge-mask encodings, and contains every edge destination. |
| [`checkHistoryBounds`](../Queens/Finite/HistoryChecking.lean#L30) | Definition 11: the mathematical well-formedness predicate is decidable. Large certificates use the verified sufficient check below for efficiency. -/ instance (graph : HistoryGraph) (memory : ℕ) : Decidable (graph.WellFormed memory) := inferInstanceAs (Decidable (_ ∧ _)) /-- Check strict binary-search ordering and bounded vertex encodings by passing an inclusive lower bound and exclusive upper bound down the tree. |
| [`checkHistoryBounds_sound`](../Queens/Finite/HistoryChecking.lean#L38) | Strict subtree bounds imply both uniqueness of vertex keys and the stated bounds on every entry. This justifies the linear uniqueness check. |
| [`historyAll`](../Queens/Finite/HistoryChecking.lean#L76) | Test a Boolean property at every history-tree entry without constructing its in-order list. This is a traversal optimization for finite verification. |
| [`historyAll_eq_true`](../Queens/Finite/HistoryChecking.lean#L79) | Tree traversal checks precisely the entries in the mathematical list view. |
| [`checkHistoryEntry`](../Queens/Finite/HistoryChecking.lean#L85) | Check an entry's edge mask and find the destination of every allowed four-symbol label. A failed lookup rejects the entry. |
| [`checkHistoryEntry_sound`](../Queens/Finite/HistoryChecking.lean#L93) | A successful entry check gives the original edge-mask bound and closure statement, using lookup soundness rather than trusting the search layout. |
| [`checkHistoryGraph`](../Queens/Finite/HistoryChecking.lean#L109) | Definition 11: an efficient executable sufficient check for the full well-formedness predicate, suitable for reduction by the Lean kernel. |
| [`checkHistoryGraph_sound`](../Queens/Finite/HistoryChecking.lean#L115) | The optimized tree checker establishes the original Definition 11, including unique vertices and closure under every allowed output symbol. |
| [`HistoryGraph.mem_of_lookup_isSome`](../Queens/Finite/HistoryChecking.lean#L126) | Definition 11: finding any mask proves that a vertex is listed. Finite prefix checks use this efficient sufficient test instead of linear membership. |

## `Queens/Finite/HistoryCore.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`HistoryGraph.edgeCount`](../Queens/Finite/HistoryCore.lean#L15) | Definition 11: count labeled edges, not merely pairs of vertices. |
| [`historyWindow`](../Queens/Finite/HistoryCore.lean#L20) | Definition 11: the window of a prescribed length ending at an absolute index. The default length is twelve, and Corollary 19 also uses forty. |
| [`HistoryGraph.FollowsThrough`](../Queens/Finite/HistoryCore.lean#L26) | Definition 11 and Section 6.1: all complete positive-index windows through `last` are vertices, and consecutive windows follow allowed labeled edges. |

## `Queens/Finite/HistoryPathChecking.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`HistoryGraph.checkFollowsThrough`](../Queens/Finite/HistoryPathChecking.lean#L15) | Definition 11: check each complete positive-index window and each following edge in a finite word prefix. Finding its mask supplies a vertex witness. |
| [`HistoryGraph.checkFollowsThrough_sound`](../Queens/Finite/HistoryPathChecking.lean#L24) | The efficient seed-word check establishes precisely the original finite path predicate, including every listed window and permitted following label. |

## `Queens/Finite/HistoryTable.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`HistoryGraph`](../Queens/Finite/HistoryTable.lean#L17) | Definition 11: the finite vertex-mask table, stored in a binary tree. The tree shape affects evaluation cost but is not a trusted invariant. |
| [`historyEntries`](../Queens/Finite/HistoryTable.lean#L24) | The untrusted binary search layout of the vertex-mask pairs. -/ tree : BinaryTree (ℕ × ℕ) deriving DecidableEq, Repr /-- In-order traversal supplies the mathematical list of history entries. This view is used for graph closure and finite cardinality assertions. |
| [`HistoryGraph.entries`](../Queens/Finite/HistoryTable.lean#L27) | Definition 11: the entries of the finite history graph. |
| [`HistoryGraph.map`](../Queens/Finite/HistoryTable.lean#L40) | Membership in a history graph means membership in its entry list. -/ instance : Membership (ℕ × ℕ) HistoryGraph where mem graph entry := entry ∈ graph.entries /-- A universal property of the finite history entries is decidable. -/ instance (graph : HistoryGraph) (P : ℕ × ℕ → Prop) [DecidablePred P] : Decidable (∀ entry ∈ graph, P entry) := inferInstanceAs (Decidable (∀ entry ∈ graph.entries, P entry)) /-- Map the entry list, for the vertex and edge counts in Proposition 17. |
| [`HistoryGraph.length`](../Queens/Finite/HistoryTable.lean#L44) | Number of listed history vertices, as in Proposition 17. |
| [`historyLookup`](../Queens/Finite/HistoryTable.lean#L48) | Search a proposed binary layout. Equality is checked before returning a mask, so malformed layouts cannot fabricate a vertex-mask pair. |
| [`HistoryGraph.lookup`](../Queens/Finite/HistoryTable.lean#L53) | Definition 11: find the allowed-symbol mask, failing when the proposed search layout does not supply that vertex. |
| [`historyLookup_mem`](../Queens/Finite/HistoryTable.lean#L58) | A successful lookup returns an actual entry, for every proposed tree. This is the soundness fact used when extending the actual word's graph path. |
| [`HistoryGraph.lookup_mem`](../Queens/Finite/HistoryTable.lean#L65) | Every successful history lookup comes from a listed vertex-mask pair, independently of balance or ordering of the generated tree. |

## `Queens/Finite/IndexedTable.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`indexed_key_eq_position`](../Queens/Finite/IndexedTable.lean#L16) | Section 6 certificate support: if the listed keys enumerate the natural range in order, the key at position `i` is precisely `i`. |
| [`indexed_mem_iff_getElem?`](../Queens/Finite/IndexedTable.lean#L26) | Section 6 certificate support: dense ordered keys turn entry membership into an exact indexed lookup, without comparing or computing the payloads. |
| [`indexed_field_getElem?`](../Queens/Finite/IndexedTable.lean#L42) | Section 6 certificate support: a listed entry's fields agree with the corresponding position in any projected list. This transfers a fast tree lookup to the public state and adjacency arrays. |

## `Queens/Finite/IndexedTree.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`indexedEntries`](../Queens/Finite/IndexedTree.lean#L15) | Section 6 certificate support: the mathematical in-order view of a tree. |
| [`indexedLookup`](../Queens/Finite/IndexedTree.lean#L21) | Section 6 certificate support: lookup checks equality before returning a value; an unsuitable search layout produces failure rather than a false match. |
| [`indexedLookup_mem`](../Queens/Finite/IndexedTree.lean#L28) | Every successful natural-number lookup identifies a listed entry. |
| [`indexedAll`](../Queens/Finite/IndexedTree.lean#L45) | Section 6 certificate support: test each entry without constructing its flattened list, so reductions follow the bounded-depth tree directly. |
| [`indexedAll_eq_true`](../Queens/Finite/IndexedTree.lean#L50) | Direct traversal verifies the predicate at every mathematical entry. |
| [`indexedLookup_of_list_alignment`](../Queens/Finite/IndexedTree.lean#L69) | A linear comparison with an indexed list, together with successful self-lookups at tree entries, identifies every requested list position. This avoids rechecking a large array separately at every index during kernel evaluation. |
| [`indexedLookup_field_eq_getElem?`](../Queens/Finite/IndexedTree.lean#L89) | A successful lookup has the field stored at its list index whenever the in-order field list agrees with the indexed mathematical list. This direction does not require a separate self-lookup check. |

## `Queens/Finite/KernelChecks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`nodup_values_of_nodup_keys`](../Queens/Finite/KernelChecks.lean#L16) | Sections 6.2–6.3: distinct keys and recovery of each key from its payload imply distinct payloads. This proves uniqueness without quadratic pair searches. |
| [`all_flatten_of_all_chunks`](../Queens/Finite/KernelChecks.lean#L29) | Sections 6.2–6.6: a Boolean predicate holds on flattened chunks whenever it holds on every chunk. This lets finite checks be split into bounded proofs. |

## `Queens/Finite/Local.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`historyLength`](../Queens/Finite/Local.lean#L27) | Section 4.3: the default number of retained symbols. The calculation also accepts an explicit history length, as needed for Corollary 19. |
| [`upperBit`](../Queens/Finite/Local.lean#L30) | Definition 9: the upper-column bit of the symbol `2u + b`. |
| [`rowBit`](../Queens/Finite/Local.lean#L33) | Definition 9: the upper-row bit of the symbol `2u + b`. |
| [`encode`](../Queens/Finite/Local.lean#L36) | Definition 11: encode a word in base four, with its newest symbol last. |
| [`decode`](../Queens/Finite/Local.lean#L39) | Definition 11: decode a fixed-length base-four history, oldest symbol first. |
| [`destination`](../Queens/Finite/Local.lean#L44) | Definition 11: dropping the oldest symbol and appending a new symbol. |
| [`hasOffset`](../Queens/Finite/Local.lean#L48) | Section 4.2: test membership in a finite set represented by a bit mask. |
| [`offsets`](../Queens/Finite/Local.lean#L52) | Section 4.2: the finite set represented by an offset bit mask. Every set bit has index below the mask itself; `mem_offsets` proves this representation exact. |
| [`mem_offsets`](../Queens/Finite/Local.lean#L56) | Section 4.2: decoding a record preserves membership exactly. |
| [`offsets_subset_Icc`](../Queens/Finite/Local.lean#L70) | Condition 15: a mask below 32 with zero low bit represents only offsets 1–4. |
| [`offsets_card_le_four`](../Queens/Finite/Local.lean#L77) | Condition 15: each bounded row or diagonal record contains at most four offsets. |
| [`insertOffset`](../Queens/Finite/Local.lean#L84) | Section 4.5: insert an offset into a bit-mask record. |
| [`State`](../Queens/Finite/Local.lean#L88) | Definition 10: the eight local records; `R`, `D`, and `A` are bit masks. `input` and `output` encode the two histories and `queue` stores symbols oldest first. |
| [`HistoryGraph.answers`](../Queens/Finite/Local.lean#L108) | Definition 10: the lower-candidate width `n - m - d`. -/ w : ℤ /-- Definition 10: displacement `n - m - U(m - 1)`. -/ z : ℤ /-- Definition 10: retained lower-queen row offsets, measured from `m`. -/ R : ℕ /-- Definition 10: retained lower-diagonal offsets, measured from `d`. -/ D : ℕ /-- Definition 10: retained lower-antidiagonal offsets, measured from `n + m`. -/ A : ℕ /-- Definition 10: the retained symbols immediately before `m`, encoded in base four. -/ input : ℕ /-- Definition 10: already read symbols beginning at `m`, oldest first. -/ queue : List ℕ /-- Definition 10: the retained symbols immediately before `n`, encoded in base four. -/ output : ℕ deriving DecidableEq, BEq, Ord, Repr /-- Definition 11: the labels allowed after an encoded input history. |
| [`Condition`](../Queens/Finite/Local.lean#L114) | Condition 15, in the bit-mask representation: the only permitted offsets of `R` and `D` are 1, 2, 3, and 4. There is no lower bound on `w`. |
| [`Condition.offsets_subset`](../Queens/Finite/Local.lean#L122) | Condition 15 is decidable from its five numerical records. -/ instance (s : State) : Decidable (Condition s) := inferInstanceAs (Decidable (_ ∧ _)) /-- Condition 15, translated from the executable masks to ordinary finite sets. |
| [`Condition.discrepancy_bound`](../Queens/Finite/Local.lean#L129) | Section 6.4: Condition 15 bounds the local lower-diagonal discrepancy. Identifying this expression with `dⱼ - j` is the board rank identity of Section 4.1. |
| [`Failure`](../Queens/Finite/Local.lean#L137) | Section 4.5: errors which invalidate the entire finite certificate. |
| [`allBranches`](../Queens/Finite/Local.lean#L147) | Algorithm 1: combine all branches, propagating any branch failure to the whole calculation. The recursive definition exposes both branch obligations. |
| [`extendBy`](../Queens/Finite/Local.lean#L157) | Algorithm 1, `Extend`: read exactly `extra` additional symbols, branching over every allowed answer. No failure is converted into an empty successor list. |
| [`extendQueue`](../Queens/Finite/Local.lean#L170) | Algorithm 1, `Extend(k)`: a negative requested length requires no extension. |
| [`historyColumns`](../Queens/Finite/Local.lean#L177) | Section 4.4: the retained upper sources before `m`, as `(h, Γ(h))`. The count at position `i` is minus the upper-column bits strictly after it. Writing this directly with a suffix sum makes the connection to `U` explicit. |
| [`queueColumns`](../Queens/Finite/Local.lean#L186) | Section 4.4: the retained upper sources at or after `m`, as `(h, Γ(h))`. The count includes the upper-column bit at `h`, hence the prefix of length `h+1`. |
| [`upperColumns`](../Queens/Finite/Local.lean#L194) | Section 4.4: all retained upper sources, as the pairs `(h, Γ(h))` used in Propositions 12–13. History sources precede queue sources, oldest first. |
| [`antidiagonalAttack`](../Queens/Finite/Local.lean#L199) | Proposition 12: the stored upper-antidiagonal attack test. |
| [`adjustment`](../Queens/Finite/Local.lean#L204) | Section 4.4 and Proposition 13: the row-count adjustment `J(x)`. |
| [`Choice`](../Queens/Finite/Local.lean#L212) | Algorithm 1: a queen choice, where `none` denotes an upper queen. |
| [`chooseFrom`](../Queens/Finite/Local.lean#L216) | Algorithm 1, the candidate loop: `remaining` is the number of candidates still to test. All failures from queue extension invalidate the calculation. |
| [`findFreeRow`](../Queens/Finite/Local.lean#L232) | Algorithm 1, the row search. Fuel exhaustion is an error, so the finite check certifies termination within this explicit bound rather than assuming it. |
| [`diagonalAdvance`](../Queens/Finite/Local.lean#L245) | Section 4.5: the least absent offset in a bit-mask diagonal record. Searching through `mask + 1` is always enough, including for the empty record. |
| [`updateState`](../Queens/Finite/Local.lean#L251) | Equation (update), Section 4.5: construct the successor after inserting a choice and finding the reference advances. `queue` includes all symbols read by the row search; `mu` of them are consumed by the new input reference. |
| [`finishChoice`](../Queens/Finite/Local.lean#L265) | Algorithm 1: finish one queen choice, check its output, and perform every branch of the row search and record update. |
| [`calculate`](../Queens/Finite/Local.lean#L286) | Algorithm 1 of Section 4.5: the complete set of branches, with multiplicity. An error in any branch is an error for the entire calculation. The row-search bound of eight is checked computationally, and never used to drop a branch. |
| [`initialState`](../Queens/Finite/Local.lean#L295) | Section 6.1: the local state before column 30, transcribed from the table. Its identification with the greedy board is proved by `initialState_represented` in `Queens.Finite.Seed`. |
| [`initialState_condition`](../Queens/Finite/Local.lean#L302) | Section 6.1: the displayed starting record satisfies Condition 15. |

## `Queens/Finite/LowerRunWitnesses.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`witnessLowerRunStart`](../Queens/Finite/LowerRunWitnesses.lean#L17) | Corollary 19: proposed start of the `k`th lower run in the checked prefix. |
| [`witnessLowerRunEnd`](../Queens/Finite/LowerRunWitnesses.lean#L21) | Corollary 19: proposed upper endpoint of the `k`th lower run. |
| [`witnessLowerRunLength`](../Queens/Finite/LowerRunWitnesses.lean#L24) | Corollary 19: the lower-run length computed from the proposed interval. |
| [`witnessLowerRunBase`](../Queens/Finite/LowerRunWitnesses.lean#L28) | Corollary 19: the search for the next lower run begins at the preceding upper endpoint, or at the origin for the first run. |
| [`CheckLowerRunInterval`](../Queens/Finite/LowerRunWitnesses.lean#L32) | Corollary 19: a proposed interval is the first nonempty lower block after its search base, with its upper endpoint verified inside the greedy prefix. |
| [`lowerRunWitnessIntervals_checked`](../Queens/Finite/LowerRunWitnesses.lean#L50) | The finite interval certificate is decidable. -/ instance (k : ℕ) : Decidable (CheckLowerRunInterval k) := inferInstanceAs (Decidable (_ ∧ _)) set_option maxRecDepth 50000 in set_option maxHeartbeats 0 in -- Kernel reduction checks the entire finite certificate at this declaration. /-- Corollary 19: every proposed initial lower-run interval is checked directly against the already certified greedy rows. |
| [`lowerRun_interval_eq_witness`](../Queens/Finite/LowerRunWitnesses.lean#L89) | Corollary 19: the finite intervals are exactly the initial intervals in the canonical infinite lower-run enumeration; no graph path is used as an occurrence. |
| [`lowerRunLength_eq_witness`](../Queens/Finite/LowerRunWitnesses.lean#L108) | Corollary 19: the first 1100 actual terms of A275885 agree with the checked finite interval table. |
| [`lowerRunEnd_twentyTwo`](../Queens/Finite/LowerRunWitnesses.lean#L118) | Corollary 19: the twenty-third lower run ends at column 80, so subsequent run-graph edges lie entirely in the forty-symbol verification. |
| [`repeatedRunWitnessStart`](../Queens/Finite/LowerRunWitnesses.lean#L124) | Corollary 19: actual starting term indices witnessing each permitted length of a maximal run of equal A275885 terms. |
| [`repeatedRunWitnessLabel`](../Queens/Finite/LowerRunWitnesses.lean#L128) | Corollary 19: the repeated A275885 term at each chosen occurrence. |
| [`repeatedRunWitnesses_checked`](../Queens/Finite/LowerRunWitnesses.lean#L136) | Corollary 19: all ten claimed repetition lengths occur in the actual-prefix run sequence, with both unequal neighboring terms checked where required. |
| [`earlyRepeatedRuns_checked`](../Queens/Finite/LowerRunWitnesses.lean#L149) | Corollary 19: every maximal repeated-term run starting before term 24 ends with a permitted length within the checked prefix. This includes all runs whose left boundary precedes the forty-symbol graph's applicability. |
| [`earlyNoTwelve_checked`](../Queens/Finite/LowerRunWitnesses.lean#L161) | Corollary 19: no initial block of twelve A275885 terms is constant. Together with the later graph bound this excludes an infinite constant final run. |

## `Queens/Finite/MaskSemantics.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`hasOffset_eq_testBit`](../Queens/Finite/MaskSemantics.lean#L15) | Section 4.2: the offset-membership test is the standard natural-number bit test. |
| [`hasOffset_shiftRight`](../Queens/Finite/MaskSemantics.lean#L21) | Section 4.5: shifting a mask advances the reference by the shift amount. |
| [`hasOffset_insertOffset`](../Queens/Finite/MaskSemantics.lean#L26) | Section 4.5: mask insertion adds exactly the requested offset. |
| [`offsets_insertOffset`](../Queens/Finite/MaskSemantics.lean#L32) | Section 4.5: mask insertion is precisely finite-set insertion. |
| [`offsets_shiftRight`](../Queens/Finite/MaskSemantics.lean#L41) | Equation (update), Section 4.5: right shift implements truncation followed by subtraction of the new reference. |
| [`diagonalAdvance_spec`](../Queens/Finite/MaskSemantics.lean#L54) | Section 4.5: the mask-based diagonal search returns the least absent nonnegative offset; its fallback is therefore unreachable. |
| [`diagonalAdvance_eq_leastUnused`](../Queens/Finite/MaskSemantics.lean#L81) | Section 4.5: the executable diagonal advance agrees with the mathematical least-unused position of its decoded record. |

## `Queens/Finite/PathContraction.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`Adjacency`](../Queens/Finite/PathContraction.lean#L15) | Appendix A: a directed graph represented by finite successor lists. |
| [`Adjacency.IsPath`](../Queens/Finite/PathContraction.lean#L18) | Appendix A: an infinite path in a finite adjacency presentation. |
| [`firstHits`](../Queens/Finite/PathContraction.lean#L24) | Appendix A: follow edges until first reaching a vertex satisfying `stop`, retaining its vertex and the number of edges. The search explores every branch up to `fuel`; exhaustion contributes no path. |
| [`firstHits_mem`](../Queens/Finite/PathContraction.lean#L32) | Appendix A: bounded first-hit search retains every path whose first stopping vertex is reached within the supplied fuel. |
| [`runTargets`](../Queens/Finite/PathContraction.lean#L70) | Appendix A: skip at most `fuel - 1` upper outputs, then follow the first lower output to its next upper endpoint. The edge label counts lower columns. |
| [`runTargets_mem`](../Queens/Finite/PathContraction.lean#L77) | Appendix A: every bounded upper-then-lower block is retained by the contracted run graph, labeled by its number of lower columns. |

## `Queens/Finite/PrefixTransfer.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`leastUnused_eq_of_spec`](../Queens/Finite/PrefixTransfer.lean#L17) | Section 6.1 and Corollary 19: a proposed least unused value is characterized by being absent while every smaller value is present. |
| [`queenSymbol_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L25) | Definition 9 on a checked prefix: the symbol in column `n` depends only on its row and the rows in earlier columns. Used for both starting-board checks. |
| [`occupiedRows_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L38) | Section 6.1 and Corollary 19: occupied rows are computed from any row function agreeing with the actual queens strictly before the current column. |
| [`earlierLowerColumns_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L45) | Section 6.1 and Corollary 19: the lower-column set can be read from a checked prefix, independently of how its row certificate was verified. |
| [`lowerDiagonals_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L70) | Section 6.1 and Corollary 19: occupied lower diagonals are exactly the positive differences read from the lower queens of a checked prefix. |
| [`rowOffsets_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L78) | Definition 10 in the starting-board checks: the row-offset record is computed from the checked prefix and the actual row reference. |
| [`antidiagonalOffsets_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L89) | Definition 10 in the starting-board checks: the antidiagonal-offset record is computed from the checked prefix and the actual row reference. |
| [`upperCount_eq_of_prefix`](../Queens/Finite/PrefixTransfer.lean#L100) | Section 6.1 and Corollary 19: the upper count through a column is computed from any prefix containing that column. |

## `Queens/Finite/Reachability.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`predecessors_checked`](../Queens/Finite/Reachability.lean#L17) | Proposition 17: every proposed predecessor witness checks successfully. The Lean kernel checks the recomputed transition and decreasing distance. |
| [`table_state_reachable`](../Queens/Finite/Reachability.lean#L43) | Proposition 17: every entry in the checked table is actually reached from the initial state. Strictly decreasing witness distances justify the induction. |
| [`certified_iff_reachable`](../Queens/Finite/Reachability.lean#L63) | Proposition 17: table membership and reachability describe exactly the same state set, rather than merely an over-approximation of the reached states. |
| [`reachable_iff_mem_states`](../Queens/Finite/Reachability.lean#L72) | Proposition 17: the mathematical set of reached states is represented by the finite state table. |
| [`reached_state_count`](../Queens/Finite/Reachability.lean#L85) | Proposition 17: there are exactly 7014 reached states. The preceding membership equivalence identifies this finite set with the actual graph reachability. |
| [`reachedEdges`](../Queens/Finite/Reachability.lean#L90) | Proposition 17: the directed edge set of the reached state graph. Successors are sets, so multiple branches producing the same target count once. |
| [`mem_reachedEdges`](../Queens/Finite/Reachability.lean#L98) | Definition 14 and Proposition 17: the finite edge set contains exactly the calculated edges whose source is reachable from the initial state. |
| [`reachedEdges_card_eq_stateEdgeCount`](../Queens/Finite/Reachability.lean#L118) | Proposition 17: summing distinct successor counts counts the reached edges exactly once. Different source vertices give disjoint sets of ordered pairs. |
| [`reached_edge_count`](../Queens/Finite/Reachability.lean#L148) | Proposition 17: there are exactly 8327 directed edges in the reached graph, with reachability and edge semantics identified by `mem_reachedEdges`. |

## `Queens/Finite/ReachabilityChunks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`predecessor_states_checked`](../Queens/Finite/ReachabilityChunks.lean#L800) | Proposition 17: every state in the candidate invariant satisfies the independently recomputed check. Each bounded check is verified by Lean's kernel; the final assembly covers every state in the original table. |

## `Queens/Finite/ReachabilityCore.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`hasStep`](../Queens/Finite/ReachabilityCore.lean#L27) | Proposition 17: a decidable test for a calculated state-graph edge. |
| [`hasStep_iff`](../Queens/Finite/ReachabilityCore.lean#L34) | Definition 14: successful executable edge testing is exactly the mathematical state-graph edge relation used by the invariant proof. |
| [`witnessDistance`](../Queens/Finite/ReachabilityCore.lean#L40) | Proposition 17: the proposed distance of a state-table entry. Defaults are harmless because every predecessor edge and strict decrease must pass the check. |
| [`witnessParent`](../Queens/Finite/ReachabilityCore.lean#L45) | Proposition 17: a proposed predecessor, with its index checked against the state table size before use. An out-of-range witness is rejected. |
| [`ParentCheck`](../Queens/Finite/ReachabilityCore.lean#L51) | Proposition 17: each entry is the initial state or has a genuine incoming edge from a table entry with a strictly smaller nonnegative distance. |
| [`predecessorIndex_alignment`](../Queens/Finite/ReachabilityCore.lean#L67) | Proposition 17: checking an individual reachability witness is decidable. -/ instance (i : Fin Data.states.size) : Decidable (ParentCheck i) := by unfold ParentCheck cases witnessParent i <;> infer_instance set_option maxHeartbeats 20000000 in -- Kernel reduction checks the complete finite certificate at this declaration. /-- Proposition 17: the balanced auxiliary table carries exactly the original predecessor array, with its natural-number positions preserved. |
| [`predecessorIndex_self_lookup`](../Queens/Finite/ReachabilityCore.lean#L76) | Proposition 17: every auxiliary predecessor record can be recovered by its own index in the proposed balanced layout. |
| [`lookupPredecessor_eq_getElem`](../Queens/Finite/ReachabilityCore.lean#L87) | Proposition 17: balanced predecessor lookup agrees with ordinary array indexing. Only the checked agreement lemmas justify this replacement. |
| [`predecessors_size`](../Queens/Finite/ReachabilityCore.lean#L96) | Proposition 17: there is one proposed predecessor record for every state. |
| [`checkParentEntry`](../Queens/Finite/ReachabilityCore.lean#L101) | Proposition 17: check a reachability witness using bounded-depth lookups. Both the actual predecessor edge and its strictly smaller distance are checked. |
| [`checkParentEntry_sound`](../Queens/Finite/ReachabilityCore.lean#L114) | Proposition 17: the optimized reachability check entails the original array-indexed witness assertion. A failed or mismatched lookup cannot supply it. |
| [`checkParentState`](../Queens/Finite/ReachabilityCore.lean#L145) | Proposition 17: check the predecessor witness of a state after recovering its checked index. Failed state lookup rejects the witness. |

## `Queens/Finite/ReachabilityData.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`predecessorIndex`](../Queens/Finite/ReachabilityData.lean#L7750) | Proposition 17: a balanced index for the auxiliary predecessor records, checked against the original array in Lean. |
| [`predecessors`](../Queens/Finite/ReachabilityData.lean#L7754) | Proposition 17: candidate distance and predecessor for each state-table index. |

## `Queens/Finite/RepeatedRunCertificate.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`repeatedRunTree_lookup_exists`](../Queens/Finite/RepeatedRunCertificate.lean#L13) | Every original state index has a corresponding run-certificate entry. |
| [`fortyStateUpper_eq`](../Queens/Finite/RepeatedRunCertificate.lean#L27) | Corollary 19: the fast upper bit is the actual output bit of the numbered state in the original forty-symbol certificate. |
| [`fortyRunAdjacency_eq`](../Queens/Finite/RepeatedRunCertificate.lean#L37) | Appendix A: the fast run-graph adjacency agrees with every successor list used in the independently checked forty-symbol state graph. |
| [`repeatedRunCertificate`](../Queens/Finite/RepeatedRunCertificate.lean#L55) | Corollary 19: the finite checks instantiate the generic, proved certificate for runs in a labeled walk. The allowed set here is the union needed by A275887. |
| [`repeatedRunLengths_nonempty`](../Queens/Finite/RepeatedRunCertificate.lean#L83) | Corollary 19: every upper-state certificate has a possible remaining length for each run label. This rules out a constant infinite tail rather than merely restricting already-terminated runs. |
| [`repeatedRunLengths_le_eleven`](../Queens/Finite/RepeatedRunCertificate.lean#L93) | Corollary 19: all remaining lengths in an upper-state certificate are at most eleven, supplying a uniform bound on constant-labeled finite paths. |

## `Queens/Finite/RepeatedRunChecks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`repeatedRunTree_self_lookup`](../Queens/Finite/RepeatedRunChecks.lean#L6674) | Corollary 19: every proposed key resolves to its exact stored payload. |
| [`repeatedRunLengthData_checked`](../Queens/Finite/RepeatedRunChecks.lean#L13329) | Corollary 19: every run-length closure and boundary obligation is kernel-checked. |
| [`repeatedRunTree_upper_alignment`](../Queens/Finite/RepeatedRunChecks.lean#L13335) | Corollary 19: the proposed upper bits agree with the original forty-symbol states. |
| [`repeatedRunTree_successor_alignment`](../Queens/Finite/RepeatedRunChecks.lean#L13344) | Corollary 19: proposed adjacency is exactly the original forty-symbol adjacency. |

## `Queens/Finite/RepeatedRunData.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`repeatedRunTree`](../Queens/Finite/RepeatedRunData.lean#L1558) | Corollary 19: balanced lookup layout for the run-graph certificate, using the reference numbering of the forty-symbol state graph. |

## `Queens/Finite/RepeatedRunDefinitions.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`fortyStateUpper`](../Queens/Finite/RepeatedRunDefinitions.lean#L15) | Corollary 19: whether a numbered forty-symbol state is immediately after an upper output. The checked balanced layout supports fast kernel lookup. |
| [`fortyRunAdjacency`](../Queens/Finite/RepeatedRunDefinitions.lean#L19) | Appendix A: original state successors read from the checked balanced layout. |
| [`repeatedRunLengths`](../Queens/Finite/RepeatedRunDefinitions.lean#L24) | Corollary 19: candidate remaining lengths for a fixed label and numbered state. The lists are untrusted certificate data until checked below. |
| [`AllowedRepeatedRunLength`](../Queens/Finite/RepeatedRunDefinitions.lean#L35) | Corollary 19, A275887: the claimed set of possible positive maximal repetition lengths. In particular the exceptional missing length is ten. |
| [`FortyRunEdge`](../Queens/Finite/RepeatedRunDefinitions.lean#L45) | The claimed set of repeated-run lengths is decidable. -/ instance (length : ℕ) : Decidable (AllowedRepeatedRunLength length) := inferInstanceAs (Decidable (_ ∧ _)) /-- Appendix A: a run-graph edge is a bounded contraction from an upper state, through at most four further upper outputs and one to three lower outputs, to the next upper output. Its label is the number of lower outputs. |
| [`CheckRepeatedRunVertex`](../Queens/Finite/RepeatedRunDefinitions.lean#L51) | Corollary 19: local closure and boundary checks for the proposed remaining length sets. Both outgoing labels and every possible remaining length are checked. |

## `Queens/Finite/RowSearch.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`wordSegment_getD`](../Queens/Finite/RowSearch.lean#L16) | Reading a present symbol from an actual word segment agrees with the absolute queen word, including the implementation's default-zero accessor. |
| [`ExtendsActualWord`](../Queens/Finite/RowSearch.lean#L25) | The semantic guarantee required of queue extension: an actual segment can be extended along the actual word to cover a request, without exceeding the range whose symbols are already known. |
| [`findFreeRow_contains_actual`](../Queens/Finite/RowSearch.lean#L34) | A successful row search retains the first actual free row. This is the operational row-search component of Section 5, Lemma 16; the queue extension hypothesis is supplied separately from the actual history-graph path. |

## `Queens/Finite/RunBounds.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`HistoryHasDifferentBit`](../Queens/Finite/RunBounds.lean#L17) | Corollary 19: the initial `length` column bits of a decoded history are not all equal to `bit`. Option-valued indexing makes this a total finite test. |
| [`historyGraph_run_bounds`](../Queens/Finite/RunBounds.lean#L29) | The finite forbidden-block test is decidable. -/ instance (history length bit : ℕ) : Decidable (HistoryHasDifferentBit history length bit) := inferInstanceAs (Decidable (∃ _i : Fin length, _)) set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in -- Kernel reduction checks the entire finite certificate at this declaration. /-- Corollary 19, exclusion bounds: no history vertex starts with four lower columns or six upper columns. This finite fact is checked using `decide +kernel`. |

## `Queens/Finite/RunVertex.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`RunVertexData`](../Queens/Finite/RunVertex.lean#L15) | Corollary 19: local data at a numbered state used by the run-graph checker. |

## `Queens/Finite/RunWitnessData.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`runWitnessRows`](../Queens/Finite/RunWitnessData.lean#L20) | Corollary 19: a proposed greedy prefix long enough to witness every value in the five-row table. Its correctness is proved in `RunWitnesses.lean`. |
| [`runWitnessRowTree`](../Queens/Finite/RunWitnessData.lean#L720) | Corollary 19: balanced lookup layout for the finite witness data. |
| [`lowerRunWitnessIntervalTree`](../Queens/Finite/RunWitnessData.lean#L819) | Corollary 19: balanced lookup layout for the finite witness data. |

## `Queens/Finite/RunWitnesses.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`runWitnessRow`](../Queens/Finite/RunWitnesses.lean#L18) | Corollary 19: access the proposed finite row certificate. |
| [`runWitnessUpper`](../Queens/Finite/RunWitnesses.lean#L21) | Corollary 19: upper columns of the finite certificate, including the origin. |
| [`runWitnessLower`](../Queens/Finite/RunWitnesses.lean#L27) | Upper-column membership in the finite witness prefix is decidable. -/ instance (n : ℕ) : Decidable (runWitnessUpper n) := inferInstanceAs (Decidable (_ ∨ _)) /-- Corollary 19: lower columns of the finite certificate. |
| [`runWitnessRows_checked`](../Queens/Finite/RunWitnesses.lean#L37) | Lower-column membership in the finite witness prefix is decidable. -/ instance (n : ℕ) : Decidable (runWitnessLower n) := inferInstanceAs (Decidable (_ < _)) set_option maxRecDepth 50000 in set_option maxHeartbeats 0 in -- Kernel reduction checks the entire finite certificate at this declaration. /-- Corollary 19: the complete finite prefix is certified by the defining greedy rule. The checker is executable, while its refinement to `q` is kernel-proved. |
| [`runWitnessRowTree_checked`](../Queens/Finite/RunWitnesses.lean#L46) | Corollary 19: the fast row lookup is a faithful layout of the same sequential row certificate. Only a linear list comparison is needed. |
| [`q_eq_runWitnessRow`](../Queens/Finite/RunWitnesses.lean#L53) | Corollary 19: every checked witness row is the actual greedy queen row. |
| [`lowerRunWitnessStart`](../Queens/Finite/RunWitnesses.lean#L67) | Corollary 19: starts of actual lower-column runs of each length 1, 2, 3. |
| [`upperRunWitnessStart`](../Queens/Finite/RunWitnesses.lean#L70) | Corollary 19: starts of actual upper-column runs of each length 1 through 5. |
| [`upperGapWitnessStart`](../Queens/Finite/RunWitnesses.lean#L73) | Corollary 19: starts of actual upper-column gaps of each length 1 through 4. |
| [`lowerGapWitnessStart`](../Queens/Finite/RunWitnesses.lean#L76) | Corollary 19: starts of actual lower-column gaps of each length 1 through 6. |
| [`basicRunWitnesses_checked`](../Queens/Finite/RunWitnesses.lean#L83) | Corollary 19, four basic attainment assertions: each listed length occurs with verified boundary columns in the actual-prefix certificate. |

## `Queens/Finite/Seed.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`seedRows`](../Queens/Finite/Seed.lean#L18) | Section 6.1: the displayed first thirty rows, used as a finite certificate. |
| [`seedRow`](../Queens/Finite/Seed.lean#L24) | Section 6.1: read an entry of the finite row certificate. |
| [`seedRows_greedy`](../Queens/Finite/Seed.lean#L28) | Section 6.1: every listed queen is exactly the least available row against the earlier entries. The finite check is reduced directly by the Lean kernel. |
| [`q_eq_seedRow`](../Queens/Finite/Seed.lean#L35) | Section 6.1: the checked finite table agrees with the actual greedy sequence in all first thirty columns. No infinite-sequence value is trusted as input. |
| [`seedSymbol`](../Queens/Finite/Seed.lean#L55) | Definition 9 evaluated on the first thirty columns, independently of the local calculation. |
| [`queenSymbol_eq_seedSymbol`](../Queens/Finite/Seed.lean#L60) | Section 6.1: the computed finite queen word is the actual queen word. |
| [`seed_discrepancy`](../Queens/Finite/Seed.lean#L66) | Section 6.1: every lower queen in the starting prefix has discrepancy at most four, measured against its lower-queen rank through the current column. |
| [`prefix_discrepancy`](../Queens/Finite/Seed.lean#L72) | Section 6.1: the finite lower-discrepancy check holds for the actual board. |
| [`occupiedRows_seed`](../Queens/Finite/Seed.lean#L85) | Section 6.1: occupied rows obtained directly from the checked prefix. |
| [`earlierLowerColumns_seed`](../Queens/Finite/Seed.lean#L89) | Section 6.1: the lower columns obtained directly from the checked prefix. |
| [`lowerDiagonals_seed`](../Queens/Finite/Seed.lean#L94) | Section 6.1: used lower diagonals obtained directly from the checked prefix. |
| [`rowReference_thirty`](../Queens/Finite/Seed.lean#L99) | Section 6.1: the actual least unused row before column 30 is 19. |
| [`diagonalReference_thirty`](../Queens/Finite/Seed.lean#L109) | Section 6.1: the actual least unused positive lower diagonal is 11. |
| [`countReference_thirty`](../Queens/Finite/Seed.lean#L121) | Section 6.1: the actual upper-count reference before column 30 is 12. |
| [`window_thirty`](../Queens/Finite/Seed.lean#L129) | Section 6.1: the actual window record is the displayed initial value. |
| [`upperDisplacement_thirty`](../Queens/Finite/Seed.lean#L133) | Section 6.1: the actual upper displacement is the displayed initial value. |
| [`rowOffsets_thirty`](../Queens/Finite/Seed.lean#L137) | Section 6.1: the actual row record before column 30 is empty. |
| [`diagonalOffsets_thirty`](../Queens/Finite/Seed.lean#L143) | Section 6.1: the actual diagonal record before column 30 consists of offset one. |
| [`antidiagonalOffsets_thirty`](../Queens/Finite/Seed.lean#L149) | Section 6.1: the actual antidiagonal record before column 30 is empty. |
| [`seedSegment`](../Queens/Finite/Seed.lean#L155) | Section 6.1: a word segment computed from the finite seed table. |
| [`wordSegment_eq_seedSegment`](../Queens/Finite/Seed.lean#L160) | Section 6.1: finite seed segments are actual queen-word segments whenever all their indices belong to the verified thirty-column prefix. |
| [`initialState_represented`](../Queens/Finite/Seed.lean#L169) | Section 6.1: all eight displayed records, including the three word fields, represent the actual board before column 30. |
| [`seedWord_follows`](../Queens/Finite/Seed.lean#L191) | Section 6.1: the seed word follows the checked history graph. |
| [`queenWord_follows_through_twentyNine`](../Queens/Finite/Seed.lean#L205) | Section 6.1: the actual queen word through column 29 follows the graph, so the initial input and output histories are grounded in the greedy board. |

## `Queens/Finite/SharpBounds.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`certified_sharpRecordCondition`](../Queens/Finite/SharpBounds.lean#L16) | Proposition 21: extract the integer record inequalities from the checked finite invariant, without an assumption about the ordering of its table. |
| [`certified_sharpChoiceCondition`](../Queens/Finite/SharpBounds.lean#L24) | Proposition 21: every choice returned by the recomputed candidate traversal satisfies the checked lower-diagonal bound. |
| [`three_halves_le_goldenRatio`](../Queens/Finite/SharpBounds.lean#L36) | Section 6.6: a simple rational lower bound for the golden ratio. |
| [`goldenRatio_le_five_thirds`](../Queens/Finite/SharpBounds.lean#L40) | Section 6.6: a simple rational upper bound for the golden ratio. |
| [`SharpRecordCondition.bounds`](../Queens/Finite/SharpBounds.lean#L45) | Proposition 21: the exact integer checks imply the required real record bounds. No numerical approximation to the golden ratio enters this argument. |

## `Queens/Finite/SharpChecks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`SharpRecordCondition`](../Queens/Finite/SharpChecks.lean#L22) | Proposition 21: integer inequalities sufficient for the record bound. The rational enclosure `3 / 2 ≤ φ ≤ 5 / 3` suffices on this invariant. |
| [`calculateChoices`](../Queens/Finite/SharpChecks.lean#L34) | Proposition 21: the integer record condition is decidable. -/ instance (s : State) : Decidable (SharpRecordCondition s) := inferInstanceAs (Decidable (_ ∧ _)) /-- Proposition 21: enumerate all candidate choices, including all preliminary input extensions. Failure propagates exactly as in Algorithm 1. |
| [`SharpChoiceCondition`](../Queens/Finite/SharpChecks.lean#L41) | Proposition 21: the upper bound on a lower choice's diagonal discrepancy. An upper choice imposes no condition on the lower diagonal. |
| [`checkSharpState`](../Queens/Finite/SharpChecks.lean#L53) | Proposition 21: the lower-choice bound is decidable by integer arithmetic. -/ instance (s : State) (choice : Choice) : Decidable (SharpChoiceCondition s choice) := by unfold SharpChoiceCondition split <;> infer_instance /-- Proposition 21: check the record bounds and every candidate choice; a failed candidate traversal rejects the state rather than discarding a branch. |

## `Queens/Finite/SharpChunks.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`sharp_certificate_checked`](../Queens/Finite/SharpChunks.lean#L800) | Proposition 21: every state in the candidate invariant satisfies the independently recomputed check. Each bounded check is verified by Lean's kernel; the final assembly covers every state in the original table. |

## `Queens/Finite/Sources.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`historyColumns_offsets_nodup`](../Queens/Finite/Sources.lean#L21) | Section 4.4: no history source is counted twice. |
| [`queueColumns_offsets_nodup`](../Queens/Finite/Sources.lean#L35) | Section 4.4: no queue source is counted twice. |
| [`historyColumns_offset_neg`](../Queens/Finite/Sources.lean#L49) | Section 4.4: every source retained in the input history is before `m`. |
| [`queueColumns_offset_nonneg`](../Queens/Finite/Sources.lean#L60) | Section 4.4: every source retained in the queue is at or after `m`. |
| [`upperColumns_offsets_nodup`](../Queens/Finite/Sources.lean#L71) | Section 4.4: each retained upper-column offset occurs exactly once in `upperColumns`; history and queue source ranges are disjoint. |
| [`upperColumns_nodup`](../Queens/Finite/Sources.lean#L84) | Section 4.4: in particular, the complete retained source pairs have no duplicates. |
| [`adjustment_eq_counts`](../Queens/Finite/Sources.lean#L91) | Proposition 13: the executable adjustment is precisely the count of queue sources below the row threshold minus history sources above that threshold. |

## `Queens/Finite/StateCountCore.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`stateSuccessorCount`](../Queens/Finite/StateCountCore.lean#L17) | Proposition 17: number of distinct successors of a state. Failed calculations contribute zero; `certified_successors` separately rules them out on the certified invariant. |
| [`stateEdgeCount`](../Queens/Finite/StateCountCore.lean#L24) | Proposition 17: sum distinct successor counts over the original invariant table. The table's checked uniqueness ensures distinct source vertices. |
| [`sum_flatten_eq_sum_ofFn`](../Queens/Finite/StateCountCore.lean#L28) | Section 6.3 certificate support: summing a function over flattened chunks is the sum of the individual chunk sums. This permits bounded kernel checks. |

## `Queens/Finite/StateCounts.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`state_edge_count`](../Queens/Finite/StateCounts.lean#L805) | Proposition 17: recomputing all distinct-successor sets gives 8327 edges. Each partial count is independently verified by the Lean kernel. |

## `Queens/Finite/StateIndex.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`stateIndexEntries`](../Queens/Finite/StateIndex.lean#L16) | Section 6.3: in-order entries of a proposed indexed state table. |
| [`lookupState`](../Queens/Finite/StateIndex.lean#L20) | Proposition 17: find a state's proposed index, checking equality at the returned node. A malformed search layout can only cause lookup failure. |
| [`lookupStateIndex`](../Queens/Finite/StateIndex.lean#L28) | Proposition 17: lookup by natural-number index, with a checked equality at the returned node. |
| [`lookupState_mem`](../Queens/Finite/StateIndex.lean#L31) | Every successful lookup by state identifies an actual indexed tree entry. |
| [`lookupStateIndex_mem`](../Queens/Finite/StateIndex.lean#L47) | Every successful lookup by index identifies an actual indexed tree entry. |
| [`stateIndexAll`](../Queens/Finite/StateIndex.lean#L53) | Sections 6.3–6.6: check a property of every indexed state directly on the tree, without materializing a large flattened array during kernel reduction. |
| [`stateIndexAll_eq_true`](../Queens/Finite/StateIndex.lean#L56) | Direct tree checks establish the predicate at every mathematical entry. |

## `Queens/Finite/StateIndexAlignment.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`stateIndex_alignment`](../Queens/Finite/StateIndexAlignment.lean#L21) | Proposition 17: the indexed tree assigns the original array position to every state. This includes both its state value and its natural-number index. |
| [`stateIndex_self_lookup`](../Queens/Finite/StateIndexAlignment.lean#L30) | Proposition 17: each proposed state-index node is found by its own index. This checks lookup completeness on the supplied layout without assuming it. |
| [`lookupStateIndex_eq_getElem`](../Queens/Finite/StateIndexAlignment.lean#L40) | Proposition 17: balanced lookup at a valid natural-number position returns exactly the state stored at that position in the original invariant array. |

## `Queens/Finite/UpdateSemantics.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`inserted_masks_represented`](../Queens/Finite/UpdateSemantics.lean#L19) | Section 4.5: recording the actual queen produces the actual three temporary sets. The lower-diagonal insertion uses signed arithmetic before conversion to its nonnegative offset. |
| [`diagonalAdvance_actual`](../Queens/Finite/UpdateSemantics.lean#L45) | Section 4.5: once the temporary diagonal mask represents the actual set, the executable least-absent-bit search finds exactly the actual advance `ν`. |
| [`updateState_records`](../Queens/Finite/UpdateSemantics.lean#L62) | Equation (update): correctly represented temporary records, actual advances, and actual consumed symbols yield all five actual numerical/set records. |
| [`updateState_represented`](../Queens/Finite/UpdateSemantics.lean#L88) | Lemma 16(ii), final update stage: actual temporary records, advances, and symbols produce a completely represented state at the next column. The strict queue bound records that the row-search stopping bit remains in the queue. |

## `Queens/FortyPath.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`RepresentsAt`](../Queens/FortyPath.lean#L19) | Corollary 19: an indexed state at time `j` represents the board before column `80 + j`, with the earlier actual word following the forty-symbol graph. |
| [`representsAt_zero`](../Queens/FortyPath.lean#L25) | Corollary 19: the checked seed establishes the refined invariant at vertex zero, before column eighty. |
| [`RepresentsAt.next`](../Queens/FortyPath.lean#L34) | Corollary 19: every represented refined state has an indexed successor representing the actual next board. No arbitrary graph path is substituted for the greedy sequence in this induction. |
| [`actualVertex`](../Queens/FortyPath.lean#L62) | Corollary 19: an indexed infinite path following the actual greedy board, with time zero immediately before column 80. |
| [`actualVertex_represents`](../Queens/FortyPath.lean#L66) | Corollary 19: each vertex of the selected path faithfully represents its actual board and all earlier forty-symbol word windows. |
| [`actualVertex_step`](../Queens/FortyPath.lean#L71) | Appendix A: consecutive vertices of the actual path are connected by a checked edge of the refined state graph. |
| [`actualVertex_output`](../Queens/FortyPath.lean#L78) | Appendix A: the output label of the indexed path is the actual column bit. Time zero records column 79, and each subsequent edge records the next column, giving the precise indexing needed when contracting lower runs. |

## `Queens/GeneralExactness.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`local_choices_exact_of_memory`](../Queens/GeneralExactness.lean#L20) | **Lemma 16, candidate phase**, also used in Proposition 21. Preliminary queue extension and candidate selection retain the actual queen choice, with a queue long enough to finish the step and containing only determined symbols. This shared statement separates candidate selection from the final record update. |
| [`local_step_exact_of_memory`](../Queens/GeneralExactness.lean#L57) | **Lemma 16 with longer histories**, as used in Corollary 19 and Appendix A. Every successful complete calculation retains the actual next board and extends the actual word's graph path. The lower bound on the upper-count reference remains twelve, independently of the retained history length. |

## `Queens/GoldenRatio.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`countError`](../Queens/GoldenRatio.lean#L21) | The error of an upper-queen count from its expected slope, as in Section 3, Proposition 8. |
| [`countDefect`](../Queens/GoldenRatio.lean#L26) | The integer recurrence's defect, viewed in the reals to avoid truncated subtraction. This is `ηₙ` in Section 3. |
| [`goldenRatio_inv_add_one`](../Queens/GoldenRatio.lean#L31) | The fixed-point identity used by the contraction arguments in Propositions 8 and 21: adding one to the inverse golden ratio gives `φ`. |
| [`countDefect_eq_error`](../Queens/GoldenRatio.lean#L40) | Cancellation of the linear terms in the counting recurrence, the algebraic identity behind the contraction in Proposition 8. |
| [`count_error_lt`](../Queens/GoldenRatio.lean#L54) | Proposition 8's count estimate, conditional on the counting recurrence. The positive-count hypothesis ensures that `n - U n` is a smaller argument, so strong induction implements the paper's contracting iteration. |
| [`upper_position_error_eq`](../Queens/GoldenRatio.lean#L91) | Sections 3 and 6.6: the upper-row identity identifies position error with count error. This algebraic step is shared by Propositions 8 and 21. |
| [`lower_position_error_eq`](../Queens/GoldenRatio.lean#L99) | Sections 3 and 6.6: splitting the lower-position error at the upper count separates the combinatorial row discrepancy from the analytic count error. |
| [`upper_position_error_lt`](../Queens/GoldenRatio.lean#L106) | The upper-position conclusion of Proposition 8, from the upper-row identity and an upper-count error bound. |
| [`lower_position_error_lt`](../Queens/GoldenRatio.lean#L113) | The lower-position conclusion of Proposition 8. The diagonal discrepancy gives `\|q - U n\| ≤ C`; adding the count error gives the stated row error. |
| [`sharp_error_bounds_of_recursion`](../Queens/GoldenRatio.lean#L128) | Proposition 21's asymmetric contraction. The term at a strictly smaller index lies in the same open interval, while the local contribution lies in the closed interval `[-4, 1]`. A finite prefix supplies the initial bounds; the paper takes `start = 30`. No finite-state assumptions enter this lemma. |

## `Queens/Greedy.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`Available`](../Queens/Greedy.lean#L22) | A row is available in column `n` against the finite list of earlier queens. The three inequalities exclude attacks along rows, diagonals, and antidiagonals. This is the greedy placement rule in the introduction. |
| [`exists_available`](../Queens/Greedy.lean#L33) | There is an available row: any row above the sum of the preceding rows plus the column index is high enough. Thus the greedy rule is defined at every column (introduction). |
| [`q`](../Queens/Greedy.lean#L46) | The greedy queens sequence `q₀, q₁, …` of the introduction: choose the least row not attacked by a queen in an earlier column. |
| [`q_available`](../Queens/Greedy.lean#L51) | The queen chosen by the greedy rule is unattacked by all earlier queens. |
| [`q_le_of_available`](../Queens/Greedy.lean#L56) | Every available row is at least the row chosen by the greedy rule. |
| [`q_safe`](../Queens/Greedy.lean#L62) | The three nonattacking conditions, stated for ordinary natural indices. |
| [`q_injective`](../Queens/Greedy.lean#L68) | Distinct columns have distinct queen rows; the injectivity part of Section 2, Lemma 3. |
| [`q_zero`](../Queens/Greedy.lean#L76) | The first queen occupies the origin (introduction). |
| [`q_one`](../Queens/Greedy.lean#L83) | The second queen is in row two (introduction). |
| [`q_ne_self`](../Queens/Greedy.lean#L95) | The queen at the origin excludes the main diagonal in every later column, so every positive-column queen is upper or lower (Section 2). |
| [`upperCount`](../Queens/Greedy.lean#L101) | Number of upper queens through column `n`, including column `n`. This is `U(n)` in the counting equation of Section 2; the origin contributes zero. |
| [`upperCount_zero`](../Queens/Greedy.lean#L105) | There are no upper queens through column zero. |
| [`upperCount_succ`](../Queens/Greedy.lean#L110) | Passing one column increases the upper count precisely when its queen is above the main diagonal. |
| [`upperCount_mono`](../Queens/Greedy.lean#L120) | Upper counts are monotone in the last column counted. |
| [`upperCount_rank_exists`](../Queens/Greedy.lean#L128) | Every positive rank up to the upper count is attained by an upper queen. This turns the count formulation of Lemma 2 into the paper's `k`th-upper-queen formulation. |
| [`q_eq_add_upperCount`](../Queens/Greedy.lean#L148) | **Lemma 2 (upper queens).** An upper queen in column `n` lies on upper diagonal `U(n)`: its row is `n + U(n)`. Equivalently, the `k`th upper queen lies on the `k`th upper diagonal. |
| [`upperCount_le`](../Queens/Greedy.lean#L184) | At most one upper queen is added in each positive column. |
| [`upperCount_pos`](../Queens/Greedy.lean#L192) | Every positive prefix contains the upper queen in column one. |
| [`q_diagonal_injective`](../Queens/Greedy.lean#L201) | Distinct queens occupy distinct signed diagonals, as required for the lower-diagonal sequence of Section 2. |
| [`q_antidiagonal_injective`](../Queens/Greedy.lean#L212) | Distinct queens occupy distinct antidiagonals. |
| [`upperCount_lt_of_upper`](../Queens/Greedy.lean#L220) | An upper queen has a larger upper rank than every earlier column. |
| [`upper_rows_gap`](../Queens/Greedy.lean#L229) | Successive upper rows differ by at least two, the observation following Section 2, Lemma 2. |

## `Queens/Identification.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`LocalStepExact`](../Queens/Identification.lean#L26) | The precise one-step correspondence of **Lemma 16**. If all branches of the finite calculation succeed, its successor list contains the actual next state, and its checked output extends the actual word's path in the history graph. The universal success hypothesis is supplied by Proposition 17 in the induction; it is not claimed to follow from Condition 15 alone. |
| [`ActualInvariant`](../Queens/Identification.lean#L37) | The three simultaneous assertions in the induction of Section 6.4: the state represents the actual board, belongs to the finite invariant, and the already determined queen word follows the history graph. |
| [`actualInvariant_thirty`](../Queens/Identification.lean#L43) | The verified starting board establishes all three assertions at column 30 (Section 6.1 and the base case of Section 6.4). |
| [`ActualInvariant.succ`](../Queens/Identification.lean#L49) | The induction step of Section 6.4, conditional only on the explicitly stated one-step correspondence. The finite checker supplies all successor bounds. |
| [`actualInvariant_of_localStepExact`](../Queens/Identification.lean#L59) | The complete infinite induction of Section 6.4. Its hypothesis is precisely the separately proved semantic correspondence in `LocalStepExact`. |
| [`nextLowerRank_lowerColumn`](../Queens/Identification.lean#L67) | The local record's next rank agrees with the positive chronological rank at a lower column. This connects equation (local-rank) to Lemma 5. |
| [`diagonalDiscrepancy_of_localStepExact`](../Queens/Identification.lean#L77) | **Lemma 5**, conditional on one-step exactness. Early columns use the direct greedy prefix check; later columns use the represented, certified state. |
| [`main_of_localStepExact`](../Queens/Identification.lean#L100) | **Theorem 1**, conditional on the single local semantic obligation of Lemma 16. The finite verification and all mathematical deductions are proved. |

## `Queens/LabeledRuns.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`ConstantLabelPath`](../Queens/LabeledRuns.lean#L19) | Corollary 19: a finite path all of whose edges carry one fixed label. |
| [`LabeledWalk`](../Queens/LabeledRuns.lean#L26) | Corollary 19: a walk with separately specified vertices and edge labels. |
| [`LabeledWalk.constantLabelPath`](../Queens/LabeledRuns.lean#L31) | For Corollary 19, a constant block in the labels of a walk gives a constant-labeled finite path between the corresponding vertices. |
| [`RunLengthCertificate`](../Queens/LabeledRuns.lean#L51) | Corollary 19: finite sets of possible lengths before a differently labeled edge. Only closure of these sets is needed, not an untrusted claim that they were computed exhaustively. `starts` handles the other boundary of a maximal run. |
| [`RunLengthCertificate.path_add_mem`](../Queens/LabeledRuns.lean#L66) | For Corollary 19, permitted numbers of `c`-edges before a first differently labeled edge. -/ lengths : Label → V → Finset ℕ /-- A different next edge terminates a constant path of length zero. -/ terminal : ∀ {v w c d}, c ∈ labels → edge v d w → d ≠ c → 0 ∈ lengths c v /-- Prepending a `c`-edge increases a permitted remaining length by one. -/ prepend : ∀ {v w c k}, c ∈ labels → edge v c w → k ∈ lengths c w → k + 1 ∈ lengths c v /-- A positive length following a different preceding edge has an allowed value. -/ starts : ∀ {u v c d k}, c ∈ labels → edge u d v → d ≠ c → k ∈ lengths c v → 0 < k → k ∈ allowed c /-- For Corollary 19, prepending a constant path to a certified remaining length adds their lengths. No different final label is required for this closure lemma. |
| [`RunLengthCertificate.path_length_mem`](../Queens/LabeledRuns.lean#L80) | The closure checks in a run-length certificate are sound for every finite constant-labeled path that ends at a differently labeled edge. |
| [`RunLengthCertificate.maximalRun_length_mem`](../Queens/LabeledRuns.lean#L91) | **Corollary 19, graph argument:** every positive-start maximal run in a walk has a length allowed by a checked certificate. Runs at index zero need separate initial-state information, just as the paper checks its initial runs. |
| [`RunLengthCertificate.constantPath_length_le`](../Queens/LabeledRuns.lean#L107) | For Corollary 19, nonempty bounded remaining-length sets bound all constant paths, including prefixes of an infinite constant tail. This justifies termination of every run. |

## `Queens/LocalAdvances.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`leastUnused_mono`](../Queens/LocalAdvances.lean#L15) | Enlarging a set of occupied positions can only increase its first gap. |
| [`rowReference_mono`](../Queens/LocalAdvances.lean#L21) | The row reference never moves backwards as new queens are placed. |
| [`diagonalReference_mono`](../Queens/LocalAdvances.lean#L27) | The lower-diagonal reference never moves backwards. |
| [`far_occupied_row_is_upper`](../Queens/LocalAdvances.lean#L36) | A row occupied before the next column and at least five positions beyond `m` can contain only an upper queen when the actual row/window bounds hold. |
| [`one_far_row_unused`](../Queens/LocalAdvances.lean#L66) | The rows at offsets five and six cannot both be occupied after the next queen is placed. This is the upper-row spacing argument in Lemma 16. |
| [`rowReference_succ_le_add_six`](../Queens/LocalAdvances.lean#L88) | **Lemma 16(iii), actual reference bound.** With the row and window parts of Condition 15, the actual least-unused-row reference advances by at most six. |

## `Queens/LocalBoard.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`exists_not_mem_finset`](../Queens/LocalBoard.lean#L20) | A finite set of natural numbers leaves some natural number unused. |
| [`leastUnused`](../Queens/LocalBoard.lean#L29) | Least natural number outside a finite set; used for the two reference positions of the actual local state in Section 4.1. |
| [`leastUnused_not_mem`](../Queens/LocalBoard.lean#L32) | The least unused position is not already occupied. |
| [`mem_of_lt_leastUnused`](../Queens/LocalBoard.lean#L36) | Every smaller position than the reference is occupied. |
| [`leastUnused_le_of_not_mem`](../Queens/LocalBoard.lean#L41) | Any unused position lies at or after the reference. |
| [`occupiedRows`](../Queens/LocalBoard.lean#L45) | Rows occupied strictly before column `n`. |
| [`rowReference`](../Queens/LocalBoard.lean#L48) | The least unused row `m` before column `n`, from Section 4.1. |
| [`earlierLowerColumns`](../Queens/LocalBoard.lean#L51) | Columns containing a lower queen strictly before column `n`. |
| [`lowerDiagonals`](../Queens/LocalBoard.lean#L55) | Positive lower-diagonal magnitudes already occupied before column `n`. |
| [`diagonalReference`](../Queens/LocalBoard.lean#L60) | The least unused positive lower-diagonal magnitude `d` in Section 4.1. Inserting zero makes ordinary least-excluded-value search positive. |
| [`window`](../Queens/LocalBoard.lean#L64) | Signed width `w = n - m - d` of the candidate window, equation (window). |
| [`countReference`](../Queens/LocalBoard.lean#L68) | Upper-count reference `κ = U(m-1)` for the actual board, Section 4.2. |
| [`upperDisplacement`](../Queens/LocalBoard.lean#L71) | Signed upper-record displacement `z = n - m - κ`, Definition 10. |
| [`rowOffsets`](../Queens/LocalBoard.lean#L75) | The actual row-offset record `R` from equation (sets). |
| [`diagonalOffsets`](../Queens/LocalBoard.lean#L80) | The actual lower-diagonal-offset record `D` from equation (sets). |
| [`antidiagonalOffsets`](../Queens/LocalBoard.lean#L85) | The actual antidiagonal-offset record `A` from equation (sets). |
| [`nextLowerRank`](../Queens/LocalBoard.lean#L91) | The positive chronological rank the next lower queen would have: one more than the number of preceding lower queens. |
| [`q_not_mem_occupiedRows`](../Queens/LocalBoard.lean#L94) | The row selected by the greedy rule has not appeared earlier. |
| [`rowReference_le_q`](../Queens/LocalBoard.lean#L101) | Every chosen row is at or above the least unused row. |
| [`rowReference_pos`](../Queens/LocalBoard.lean#L105) | After the origin has been placed, the row reference is positive. |
| [`lowerDiagonal_pos`](../Queens/LocalBoard.lean#L115) | Every used lower-diagonal magnitude is positive. |
| [`zero_not_mem_lowerDiagonals`](../Queens/LocalBoard.lean#L121) | The main diagonal is not one of the positive lower diagonals. |
| [`diagonalReference_pos`](../Queens/LocalBoard.lean#L127) | The lower-diagonal reference is always positive. |
| [`diagonalReference_not_mem`](../Queens/LocalBoard.lean#L135) | The reference lower diagonal is unused. |
| [`mem_lowerDiagonals_of_lt_reference`](../Queens/LocalBoard.lean#L139) | Every positive lower diagonal below the reference is occupied. |
| [`lowerDiagonal_injOn`](../Queens/LocalBoard.lean#L147) | Earlier lower queens have distinct lower-diagonal magnitudes. |
| [`lowerDiagonals_card`](../Queens/LocalBoard.lean#L158) | Counting occupied lower diagonals counts exactly the earlier lower queens. |
| [`lowerDiagonals_below_reference`](../Queens/LocalBoard.lean#L163) | The occupied lower magnitudes below `d` are exactly `1, …, d-1`. |
| [`diagonalOffsets_card`](../Queens/LocalBoard.lean#L175) | Offsetting the retained diagonal magnitudes preserves their cardinality. |
| [`nextLowerRank_eq_reference_add_offsets`](../Queens/LocalBoard.lean#L187) | The first identity in equation (local-rank): the next lower rank is `j = d + \|D\|`, because precisely `d-1` smaller magnitudes have been used. |
| [`q_lowerDiagonal_not_mem`](../Queens/LocalBoard.lean#L199) | A newly placed lower queen uses a previously unused lower diagonal. |
| [`diagonalReference_le_lowerDiagonal`](../Queens/LocalBoard.lean#L210) | The diagonal of a lower placement lies at or beyond the current least unused lower-diagonal reference. |
| [`rowOffset`](../Queens/LocalBoard.lean#L220) | The actual offset of a new queen from the least unused row. For a lower queen it is one of the candidate offsets in Section 4.1. |
| [`rowOffset_le_window`](../Queens/LocalBoard.lean#L223) | A lower placement's offset lies in the candidate window `0 ≤ r ≤ w`. |
| [`local_rank_identity`](../Queens/LocalBoard.lean#L231) | Equation (local-rank): the lower-diagonal discrepancy is exactly `w - r - \|D\|`, with all records defined from the actual greedy board. |
| [`DiagonalRecordBounds`](../Queens/LocalBoard.lean#L242) | The portion of Condition 15 used for diagonal discrepancy: `w ≤ 4` and `D ⊆ {1,2,3,4}`. The remaining bounds ensure sufficiency of the local step but are not needed for this arithmetic consequence. |
| [`discrepancy_of_record_bounds`](../Queens/LocalBoard.lean#L247) | Extraction of Lemma 5 from the actual-record bounds, as in Section 6.4. This theorem does not assume that an abstract finite state is the actual board. |

## `Queens/LocalBounds.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`countReference_mono`](../Queens/LocalBounds.lean#L18) | The actual upper-count reference never decreases as the board grows. This propagates the starting inequality `κ ≥ 12` in Section 6.4. |
| [`rowReference_ge_nineteen`](../Queens/LocalBounds.lean#L24) | The starting row reference is 19, and later row references are no smaller. Thus all later twelve-symbol input histories have positive indices. |
| [`countReference_ge_twelve`](../Queens/LocalBounds.lean#L30) | The upper-count reference stays at least twelve after the verified start, as required by Lemma 16. |
| [`StateRepresented.requests_causal_general`](../Queens/LocalBounds.lean#L37) | Under Condition 15 and `κ ≥ 12`, every symbol through offset six is already determined. This is the strict causality inequality of Lemma 16(i), independent of the history length used in the forty-symbol extension of Corollary 19. |
| [`StateRepresented.requests_causal`](../Queens/LocalBounds.lean#L48) | Lemma 16(i): the checked starting board supplies the count bound needed for causality in the twelve-symbol calculation from column 30 onwards. |
| [`StateRepresented.extendsActualWord_general`](../Queens/LocalBounds.lean#L56) | The actual history graph path supplies the queue-extension guarantee used by the executable candidate and row-search loops (Lemma 16(i)). The history length and graph are arbitrary, as required by Corollary 19's larger graph. |
| [`StateRepresented.extendsActualWord`](../Queens/LocalBounds.lean#L74) | Lemma 16(i): queue extension along the checked twelve-symbol graph retains the actual word after the verified starting column. |

## `Queens/LocalCandidates.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`available_not_mem_occupiedRows`](../Queens/LocalCandidates.lean#L17) | An available square cannot use any previously occupied row. |
| [`rowReference_le_of_available`](../Queens/LocalCandidates.lean#L25) | The least unused row is a lower bound for every available square, as used in Section 4.1 to restrict the candidate window. |
| [`available_lowerDiagonal_not_mem`](../Queens/LocalCandidates.lean#L30) | An available lower square lies on an unused positive lower diagonal. |
| [`diagonalReference_le_of_available`](../Queens/LocalCandidates.lean#L43) | The least unused positive lower diagonal bounds every available lower square, giving the right endpoint `n - d` in Section 4.1. |
| [`available_lower_in_window`](../Queens/LocalCandidates.lean#L54) | Every available lower row belongs to the candidate interval `[m, n-d]` of Section 4.1. This statement concerns all available rows, not just `q n`. |
| [`candidate_row_lt`](../Queens/LocalCandidates.lean#L67) | Every offset in the candidate window gives a square strictly below the main diagonal; positivity of the least unused diagonal is essential here. |
| [`upper_of_window_neg`](../Queens/LocalCandidates.lean#L75) | A negative candidate width forces an upper queen in every positive column, as stated in Section 4.1. |
| [`mem_rowOffsets_iff`](../Queens/LocalCandidates.lean#L84) | The row record `R` detects exactly the earlier lower queens sharing a candidate's row, the first attack test in Section 4.1. |
| [`mem_antidiagonalOffsets_iff`](../Queens/LocalCandidates.lean#L99) | The antidiagonal record `A` detects exactly the earlier lower queens sharing a candidate's antidiagonal, the third attack test in Section 4.1. |
| [`mem_diagonalOffsets_iff`](../Queens/LocalCandidates.lean#L116) | The diagonal record `D` detects exactly the earlier lower queens sharing a candidate's diagonal, the second attack test in Section 4.1. The conversion to a natural offset is valid because `r ≤ w`. |
| [`zero_not_mem_rowOffsets`](../Queens/LocalCandidates.lean#L141) | Offset zero never occurs in `R`: its reference is the least unused row. |
| [`zero_not_mem_diagonalOffsets`](../Queens/LocalCandidates.lean#L149) | Offset zero never occurs in `D`: its reference is an unused lower diagonal. |
| [`LowerCandidateClear`](../Queens/LocalCandidates.lean#L159) | The five attack tests for a lower candidate in Sections 4.1–4.4. The last test still ranges over actual upper queens; restricting it to the retained history and queue is a separate sufficiency argument in Lemma 16. |
| [`available_candidate_iff`](../Queens/LocalCandidates.lean#L169) | A lower candidate is available exactly when all five local attack tests pass. This includes the origin and the impossibility of an upper queen attacking a lower square along a diagonal, as required by Lemma 16. |
| [`q_eq_candidate_iff`](../Queens/LocalCandidates.lean#L228) | The actual lower choice is precisely the first candidate passing the five tests. This proves the candidate-selection part of Lemma 16 without assuming that the finite calculation already represents the greedy board. |
| [`q_upper_iff_no_clear_candidate`](../Queens/LocalCandidates.lean#L252) | The actual queen is upper exactly when no offset in the lower-candidate window passes the five tests, including when the window has negative width. |

## `Queens/LocalChoice.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`ChoiceMatches`](../Queens/LocalChoice.lean#L17) | Agreement of an optional finite-calculation choice with the actual queen. `none` denotes an upper queen and `some r` denotes the lower row `m + r`. |
| [`ChoiceMatches.eq_actual`](../Queens/LocalChoice.lean#L23) | A matching optional choice is exactly the actual lower offset when the queen is lower, and `none` otherwise. This normal form feeds the record updates. |
| [`chooseFrom_actual_step`](../Queens/LocalChoice.lean#L51) | One successful iteration on an actual queue either retains this available candidate, or retains a recursive continuation and this candidate is attacked. This is the local operational step in the choice part of Lemma 16. |
| [`chooseFrom_contains_actual_lower`](../Queens/LocalChoice.lean#L133) | A successful candidate loop retains the actual lower queen whenever the searched interval reaches its offset and begins at or before it. Earlier available candidates are excluded by the defining greedy minimality. |
| [`chooseFrom_contains_actual_upper`](../Queens/LocalChoice.lean#L166) | If the actual queen is upper, every tested lower candidate is attacked. A successful loop therefore retains the upper choice and its actual queue. |
| [`chooseFrom_contains_actual`](../Queens/LocalChoice.lean#L198) | **Lemma 16, candidate choice.** Starting at offset zero and testing the whole candidate window, the successful branching calculation contains a choice matching the actual greedy queen and an actual extended queue. |

## `Queens/LocalGeometry.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`relativeUpperCount`](../Queens/LocalGeometry.lean#L20) | The signed upper-count difference `Γ` from Section 4.4, evaluated at an absolute column `i` relative to the reference row `m`. |
| [`upper_row_relative`](../Queens/LocalGeometry.lean#L24) | The relative-row identity in equation (source-offsets), Section 4.4. |
| [`upper_antidiagonal_relative`](../Queens/LocalGeometry.lean#L32) | The relative-antidiagonal identity in equation (source-offsets), Section 4.4. |
| [`upper_antidiagonal_test`](../Queens/LocalGeometry.lean#L42) | The upper-antidiagonal test of **Proposition 12**, before restricting to retained source columns. An upper queen attacks `(n, m + r)` exactly when `2h + Γ(h) = z + r`. |
| [`relativeUpperCount_nonpos`](../Queens/LocalGeometry.lean#L51) | Upper-count differences are nonpositive to the left of the row reference. This is the observation about `Γ(h)` for negative offsets in Sections 4–5. |
| [`relativeUpperCount_pos`](../Queens/LocalGeometry.lean#L59) | An upper source at or after the row reference contributes its own upper column, so `Γ(h) ≥ 1`; used to exclude sources beyond the queue in Lemma 16. |
| [`old_upper_source_irrelevant`](../Queens/LocalGeometry.lean#L68) | An upper source before the twelve-symbol input history is below both row thresholds and cannot attack a lower candidate's antidiagonal. These are the old-source exclusions in **Lemma 16**. |
| [`future_upper_row_above`](../Queens/LocalGeometry.lean#L80) | An upper source beyond a queue of length at least `z` lies above the row threshold `n`. This justifies omitting future sources from Proposition 13's row-count adjustment in the proof of Lemma 16. |
| [`future_upper_antidiagonal_above`](../Queens/LocalGeometry.lean#L90) | The candidate extension length excludes every upper source after the queue from its antidiagonal attack test, as proved in Lemma 16. |
| [`not_consecutive_upper_rows`](../Queens/LocalGeometry.lean#L100) | No two consecutive rows are upper rows, the observation after Lemma 2 used to terminate the row search in Lemma 16. |
| [`candidate_request_le_four`](../Queens/LocalGeometry.lean#L113) | The candidate loop only requests offsets through four under Condition 15. This is the candidate-request estimate in Lemma 16. |
| [`request_before_current_column`](../Queens/LocalGeometry.lean#L120) | The causality estimate in Lemma 16: with `κ ≥ 12` and `z ≥ -4`, every request at most six places beyond `m` concerns a column already determined. |
| [`exists_free_offset_le_six`](../Queens/LocalGeometry.lean#L128) | The row search has an available offset by six: a lower-row record and the newly chosen lower queen occupy offsets at most four, and at least one of rows `m + 5`, `m + 6` is not upper. This is the existence argument for part (iii) of Lemma 16. |

## `Queens/LocalRepresentation.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`RecordsRepresented`](../Queens/LocalRepresentation.lean#L20) | Agreement of the five numerical and set records of Definition 10 with the actual board before column `n`. Word histories and the queue are separate parts of the full local-state interpretation. |
| [`RecordsRepresented.diagonalRecordBounds`](../Queens/LocalRepresentation.lean#L34) | The signed candidate-window width agrees. -/ window_eq : window n = s.w /-- The signed upper-count displacement agrees. -/ upperDisplacement_eq : upperDisplacement n = s.z /-- The row bit mask represents precisely the actual retained row offsets. -/ rowOffsets_eq : rowOffsets n = Finite.offsets s.R /-- The diagonal bit mask represents precisely the actual retained diagonal offsets. -/ diagonalOffsets_eq : diagonalOffsets n = Finite.offsets s.D /-- The antidiagonal bit mask represents precisely the actual retained offsets. -/ antidiagonalOffsets_eq : antidiagonalOffsets n = Finite.offsets s.A /-- Condition 15 on a faithfully represented finite state gives the actual record bounds needed to extract the diagonal discrepancy. |
| [`discrepancy_of_represented_condition`](../Queens/LocalRepresentation.lean#L45) | A represented finite state satisfying Condition 15 proves the discrepancy bound for the actual lower queen in that column (Section 6.4). |
| [`wordSegment`](../Queens/LocalRepresentation.lean#L53) | A consecutive finite segment of the actual queen word, with its starting index retained explicitly. History and queue lengths are explicit parameters. |
| [`wordSegment_length`](../Queens/LocalRepresentation.lean#L57) | An actual word segment has exactly the requested number of symbols. |
| [`wordSegment_getElem`](../Queens/LocalRepresentation.lean#L61) | Reading within a word segment returns the symbol at its absolute index. |
| [`wordSegment_add`](../Queens/LocalRepresentation.lean#L66) | Adjacent actual word segments concatenate to the segment of combined length. |
| [`wordSegment_take`](../Queens/LocalRepresentation.lean#L71) | Taking an initial segment preserves its absolute starting index. |
| [`wordSegment_drop`](../Queens/LocalRepresentation.lean#L77) | Consuming symbols advances a segment's starting index by the number consumed. |
| [`upperBit_queenSymbol`](../Queens/LocalRepresentation.lean#L85) | Decoding the column bit of an actual symbol recovers the upper-column indicator. |
| [`rowBit_queenSymbol`](../Queens/LocalRepresentation.lean#L92) | Decoding the row bit of an actual symbol recovers the upper-row indicator. |
| [`StateRepresented`](../Queens/LocalRepresentation.lean#L101) | Full interpretation of a local state before column `n`: five actual records, two actual histories of the specified length, and a nonempty actual queue. The queue ends before the next column, as required in Lemma 16. |
| [`StateRepresented.queue_getElem`](../Queens/LocalRepresentation.lean#L120) | The input history starts at a nonnegative absolute index. -/ history_start : memory ≤ rowReference n /-- The input history contains precisely the stored symbols preceding `m`. -/ input_eq : Finite.encode (wordSegment (rowReference n - memory) memory) = s.input /-- The queue contains consecutive actual symbols starting at `m`. -/ queue_eq : wordSegment (rowReference n) s.queue.length = s.queue /-- The output history contains precisely the stored symbols preceding `n`. -/ output_eq : Finite.encode (wordSegment (n - memory) memory) = s.output /-- A local queue is nonempty (Definition 10). -/ queue_nonempty : 0 < s.queue.length /-- Every queued symbol is determined by the already placed queens. -/ queue_before_column : rowReference n + s.queue.length ≤ n /-- Every queued symbol in a represented state is the actual symbol at the corresponding absolute index. |

## `Queens/LocalRequests.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`wordSegment_symbols_lt_four`](../Queens/LocalRequests.lean#L18) | Every symbol in an actual word segment lies in the four-symbol alphabet (Definition 9). |
| [`inputHistoryAt`](../Queens/LocalRequests.lean#L26) | The encoded history immediately before an absolute input position. This is the input vertex used for requests in Section 4.3. |
| [`fold_destination_wordSegment`](../Queens/LocalRequests.lean#L31) | Appending an actual word segment advances its encoded history to the end of that segment, keeping the last `memory` symbols (Section 4.5). |
| [`destination_inputHistoryAt`](../Queens/LocalRequests.lean#L47) | Advancing one actual symbol shifts the preceding history to the next input position (Section 4.3). |
| [`historyWindow_previous`](../Queens/LocalRequests.lean#L56) | The history-window convention in Definition 11 agrees with the input history immediately before the next symbol. |
| [`permittedPath_wordSegment`](../Queens/LocalRequests.lean#L64) | The actual word supplies a permitted path for every requested segment whose symbols are already determined. This is Lemma 16(i)'s graph-path argument. |
| [`extendBy_contains_actual`](../Queens/LocalRequests.lean#L93) | If `Extend` succeeds, its output includes the actual extended queue. Every permitted answer is retained by the generic branching calculation, so the true board branch cannot disappear (Lemma 16(i)). |
| [`extendQueue_contains_actual`](../Queens/LocalRequests.lean#L110) | The exact actual-queue length after a successful `Extend(k)` is the maximum of the previous length and the requested nonnegative length. Requests already satisfied by the queue leave the actual branch unchanged (Algorithm 1). |
| [`StateRepresented.output_last`](../Queens/LocalRequests.lean#L126) | The last digit of a represented output history is the actual previous queen symbol. This links local-state graph labels to the sequence in Corollary 19's path-contraction argument. |

## `Queens/LocalSources.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`wordSegment_one`](../Queens/LocalSources.lean#L20) | A single-symbol segment contains exactly the symbol at its start. |
| [`sum_upperBits_wordSegment`](../Queens/LocalSources.lean#L27) | Summing upper-column bits over a positive-index actual segment gives the change in the upper count. This is the prefix/suffix interpretation of `Γ` in equation (C), Section 4.4. |
| [`queue_prefix_upperCount`](../Queens/LocalSources.lean#L46) | Prefix bits through a retained queue column give its relative upper count. This is the nonnegative-offset part of equation (C). |
| [`history_suffix_upperCount`](../Queens/LocalSources.lean#L58) | Suffix bits strictly after a retained history column give the negative of its relative count. This is the negative-offset part of equation (C). |
| [`mem_queueColumns_wordSegment`](../Queens/LocalSources.lean#L83) | The executable queue-source list contains exactly the actual upper columns in the queue, with their correct relative counts. |
| [`mem_historyColumns_wordSegment`](../Queens/LocalSources.lean#L101) | The executable history-source list contains exactly the actual upper columns in the input history, with their correct negative relative counts. |
| [`StateRepresented.decode_input`](../Queens/LocalSources.lean#L121) | Decoding a represented input history recovers the actual stored segment. The base-four representation is justified by the four-symbol bound. |
| [`StateRepresented.mem_upperColumns`](../Queens/LocalSources.lean#L137) | The stored source list represents exactly the actual upper queens in the retained interval. This is the semantic link from the finite source computation to the coordinates of Propositions 12–13. |
| [`upper_antidiagonal_retained_iff`](../Queens/LocalSources.lean#L186) | Under Lemma 16's lower bound on `z` and the candidate queue-extension bound, all attacking upper queens lie in the retained history and queue. The right side is exactly Proposition 12's relative-coordinate test. |
| [`StateRepresented.antidiagonalAttack_iff`](../Queens/LocalSources.lean#L219) | **Proposition 12 for the finite calculation.** When the input history and queue are actual word segments and the request bound is met, the executable upper-antidiagonal test detects exactly actual earlier attacks. |
| [`StateRepresented.upperColumns_toFinset`](../Queens/LocalSources.lean#L245) | As a finite set, the retained source list is the injective image of the actual retained upper columns under their relative-coordinate map. |
| [`StateRepresented.upperColumns_filter_card`](../Queens/LocalSources.lean#L267) | Counting retained source pairs satisfying a test is the same as counting the corresponding actual upper columns. This injective-image fact supplies the two finite cardinalities in Proposition 13. |
| [`StateRepresented.upperColumns_addition_card`](../Queens/LocalSources.lean#L285) | The nonnegative-offset part of `J(T-m-κ)` counts exactly the upper rows at or below `T` coming from queue columns, as in Proposition 13. |
| [`StateRepresented.upperColumns_removal_card`](../Queens/LocalSources.lean#L311) | The negative-offset part of `J(T-m-κ)` counts exactly the upper rows above `T` whose columns lie in the input history, as in Proposition 13. |
| [`StateRepresented.adjustment_eq_upperRowCount`](../Queens/LocalSources.lean#L344) | **Proposition 13 for the executable source list.** Assuming the omitted old and future sources lie on the stated sides of the row threshold, the finite adjustment computes the actual upper-row count minus `κ`. |
| [`StateRepresented.adjustment_eq_upperRowCount_near_column`](../Queens/LocalSources.lean#L370) | Under Lemma 16's bounds, the finite adjustment gives the actual row count at either output threshold, `n - 1` or `n`. |
| [`StateRepresented.adjustment_difference_eq_upperRowBit`](../Queens/LocalSources.lean#L395) | The output bit computed by Algorithm 1 agrees with the actual row bit. This is the output-symbol part of Lemma 16, combining Proposition 13 at the two adjacent thresholds. |
| [`StateRepresented.candidate_tests_iff`](../Queens/LocalSources.lean#L420) | All executable candidate tests agree with actual availability when the extended queue is an actual segment long enough for the requested candidate. This combines the set-mask representation, queue row bit, and Proposition 12 into the exact test used in Algorithm 1's candidate loop. |

## `Queens/LocalUpdates.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`retainedOffsets`](../Queens/LocalUpdates.lean#L16) | Retain only values at or beyond a reference and subtract that reference. This is the common operation defining all three local offset records. |
| [`mem_retainedOffsets`](../Queens/LocalUpdates.lean#L20) | Membership in a translated, truncated set of offsets. |
| [`retainedOffsets_add`](../Queens/LocalUpdates.lean#L27) | Advancing a reference twice is the same as advancing it by the sum. This is the set-level meaning of successive bit-mask shifts. |
| [`retainedOffsets_insert`](../Queens/LocalUpdates.lean#L39) | Inserting a value at or above the reference inserts precisely its offset. |
| [`lowerRowsBefore`](../Queens/LocalUpdates.lean#L44) | Positive-lower rows already occupied before column `n`. |
| [`lowerAntidiagonalsBefore`](../Queens/LocalUpdates.lean#L47) | Antidiagonal indices of the earlier lower queens. |
| [`rowOffsets_eq_retained`](../Queens/LocalUpdates.lean#L51) | Normalize `R` as reference subtraction on the set of earlier lower rows. |
| [`diagonalOffsets_eq_retained`](../Queens/LocalUpdates.lean#L63) | Normalize `D` as reference subtraction on the earlier lower diagonals. |
| [`antidiagonalOffsets_eq_retained`](../Queens/LocalUpdates.lean#L67) | Normalize `A` as reference subtraction on the earlier lower antidiagonals. |
| [`earlierLowerColumns_succ`](../Queens/LocalUpdates.lean#L79) | The next column adds to the lower-column set exactly for a lower queen. |
| [`insertedRowOffsets`](../Queens/LocalUpdates.lean#L87) | The temporary row record after inserting the current lower choice. |
| [`insertedDiagonalOffsets`](../Queens/LocalUpdates.lean#L91) | The temporary diagonal record after inserting the current lower choice. |
| [`insertedAntidiagonalOffsets`](../Queens/LocalUpdates.lean#L96) | The temporary antidiagonal record after inserting the current lower choice. |
| [`insertedRowOffsets_eq`](../Queens/LocalUpdates.lean#L100) | Insertion into `R` is precisely the new row set measured at the old reference. |
| [`insertedDiagonalOffsets_eq`](../Queens/LocalUpdates.lean#L110) | Insertion into `D` is precisely the new diagonal set measured at the old reference. |
| [`insertedAntidiagonalOffsets_eq`](../Queens/LocalUpdates.lean#L121) | Insertion into `A` is precisely the new antidiagonal set measured at the old reference. |
| [`rowAdvance`](../Queens/LocalUpdates.lean#L135) | The actual row-reference advance `μ`, Section 4.5. |
| [`lowerDiagonalAdvance`](../Queens/LocalUpdates.lean#L138) | The actual lower-diagonal-reference advance `ν`, Section 4.5. |
| [`rowReference_add_advance`](../Queens/LocalUpdates.lean#L142) | Advancing by `μ` reaches the next actual row reference. |
| [`diagonalReference_add_advance`](../Queens/LocalUpdates.lean#L149) | Advancing by `ν` reaches the next actual diagonal reference. |
| [`rowOffsets_succ`](../Queens/LocalUpdates.lean#L157) | Equation (update), the actual row record: insert the new lower choice, then discard and translate offsets by `μ`. |
| [`diagonalOffsets_succ`](../Queens/LocalUpdates.lean#L164) | Equation (update), the actual diagonal record: insert the new lower choice, then discard and translate offsets by `ν`. |
| [`antidiagonalOffsets_succ`](../Queens/LocalUpdates.lean#L172) | Equation (update), the actual antidiagonal record: its reference advances by `1 + μ`, because both the column and row reference move. |
| [`window_succ`](../Queens/LocalUpdates.lean#L181) | Equation (update), the signed candidate-window width. |
| [`upperDisplacement_succ`](../Queens/LocalUpdates.lean#L190) | Equation (update), the signed upper-count displacement, before rewriting the count increment as the sum of the consumed column bits. |
| [`upperCount_eq_pred_add_columnBit`](../Queens/LocalUpdates.lean#L198) | The upper count increases by the column bit at each positive column. |
| [`upperCount_add_segment_sum`](../Queens/LocalUpdates.lean#L205) | The column bits in a consumed actual word segment record precisely the increase in the upper count. This supplies `Δu` in equation (update). |
| [`countReference_succ`](../Queens/LocalUpdates.lean#L223) | The upper-count reference changes by the sum of the `μ` consumed column bits, exactly as Algorithm 1 computes it. |
| [`upperDisplacement_succ_word`](../Queens/LocalUpdates.lean#L231) | Equation (update), including the word-based computation of `Δu`. |
| [`mem_insertedRowOffsets`](../Queens/LocalUpdates.lean#L240) | The temporary row offsets exactly describe lower queens through the current column, still measured relative to the old row reference. |
| [`occupied_row_iff_inserted_or_upper`](../Queens/LocalUpdates.lean#L254) | Within the already determined part of the word, a positive row is occupied precisely when its lower-record bit or upper-row bit is set. |
| [`rowAdvance_le_six`](../Queens/LocalUpdates.lean#L279) | The actual advance `μ` is at most six under the bounds used by Lemma 16. |
| [`rowAdvance_free`](../Queens/LocalUpdates.lean#L287) | The actual row search stops at `μ`: its temporary lower-row record and actual upper-row bit are both zero there (Lemma 16). |
| [`rowAdvance_minimal`](../Queens/LocalUpdates.lean#L306) | Every smaller row offset fails the temporary-record/upper-bit search. Together with `rowAdvance_free`, this identifies its least successful offset. |
| [`lowerDiagonalAdvance_free`](../Queens/LocalUpdates.lean#L319) | The actual diagonal advance `ν` is the first unused temporary diagonal offset. This is the mathematical specification of `diagonalAdvance`. |
| [`lowerDiagonalAdvance_minimal`](../Queens/LocalUpdates.lean#L328) | Every diagonal offset below `ν` is occupied in the temporary record. |

## `Queens/LowerColumns.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`lowerColumn`](../Queens/LowerColumns.lean#L17) | The lower queen's column at zero-based chronological rank `k`. Thus this is `xᴸₖ₊₁` in Sections 2 and 3. |
| [`lowerCount`](../Queens/LowerColumns.lean#L22) | Number of lower queens through column `n`, written as the complementary count `L(n) = n - U(n)` from Section 3. The origin counts as neither type. |
| [`lowerColumn_strictMono`](../Queens/LowerColumns.lean#L25) | The chronological lower-column enumeration is strictly increasing. |
| [`lowerColumn_lower`](../Queens/LowerColumns.lean#L29) | Every term of the lower-column enumeration contains a lower queen. |
| [`exists_lowerColumn_eq`](../Queens/LowerColumns.lean#L33) | Every lower queen appears in the chronological lower-column enumeration. |
| [`count_lower_eq_lowerCount`](../Queens/LowerColumns.lean#L38) | The complementary count really counts lower queens. The offset by one comes from `Nat.count` excluding its upper endpoint. |
| [`lowerCount_lowerColumn`](../Queens/LowerColumns.lean#L58) | At the `k`th zero-based lower column, exactly `k + 1` lower queens have appeared. This is the rank identity used in Section 3. |
| [`lowerColumn_eq_upperCount_add_rank`](../Queens/LowerColumns.lean#L65) | Section 3's rank identity: the column is the number of upper queens plus the positive rank of its lower queen. The origin contributes neither count. |
| [`upperCount_lowerColumn`](../Queens/LowerColumns.lean#L75) | The upper count at a lower column is the column minus its positive rank: `U(xᴸⱼ) = xᴸⱼ - j`, as used in equation (rank-row) of Section 3. |
| [`lowerColumn_upperCount_mono`](../Queens/LowerColumns.lean#L82) | The comparison sequence `tₖ = U(xᴸₖ₊₁)` is monotone, the order hypothesis needed by the sorting argument in Section 3, Lemma 6. |
| [`lower_row_count_identity`](../Queens/LowerColumns.lean#L88) | The rank-row identity from Section 3: the error of a lower row from the upper count is the negative of its diagonal-magnitude error from its rank. |
| [`lower_row_count_discrepancy`](../Queens/LowerColumns.lean#L96) | Diagonal discrepancy and chronological lower-row discrepancy are the same absolute error, by the rank-row identity in Section 3. |
| [`lowerColumn_left`](../Queens/LowerColumns.lean#L105) | If at least one lower queen has appeared, its last lower column is at most the current column. This is the left endpoint used in Lemma 7. |
| [`lowerColumn_right`](../Queens/LowerColumns.lean#L114) | The next lower column lies strictly after the current column. This is the right endpoint used in Section 3, Lemma 7, also when the lower count is zero. |

## `Queens/LowerRows.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`IsLowerRow`](../Queens/LowerRows.lean#L19) | A row occupied by a lower queen, as in Section 2. |
| [`sortedLowerRow`](../Queens/LowerRows.lean#L23) | The lower rows in increasing order. This is `vⱼ` in Section 2, with Lean index `k` corresponding to the paper's positive index `j = k + 1`. |
| [`infinite_lowerRows`](../Queens/LowerRows.lean#L99) | Infinitely many rows are occupied by lower queens. This justifies the sorted enumeration introduced after Lemma 3 in Section 2. |
| [`sortedLowerRow_eq`](../Queens/LowerRows.lean#L106) | **Lemma 4 (sorted lower rows).** With zero-based indexing, `v(k) = k + 1 + U(k)`. The row permutation hypothesis is Lemma 3. |
| [`sortedLowerRow_strictMono`](../Queens/LowerRows.lean#L120) | The sorted lower-row sequence is strictly increasing (Section 2). |
| [`range_sortedLowerRow`](../Queens/LowerRows.lean#L125) | Sorting neither loses nor adds lower rows (Section 2). |
| [`infinite_lowerColumns`](../Queens/LowerRows.lean#L131) | There are infinitely many lower columns, as asserted after Lemma 3 in Section 2. Their image under `q` is the infinite set of lower rows. |

## `Queens/LowerRunCoverage.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`exists_lowerRun_contains`](../Queens/LowerRunCoverage.lean#L16) | Every actual lower column belongs to one of the canonical lower runs. The least endpoint after the column identifies the required run. |
| [`lowerRunEnd_lt_start_of_lt`](../Queens/LowerRunCoverage.lean#L40) | Distinct enumerated lower runs are disjoint and occur in increasing order, with a nonempty upper block between them. |
| [`existsUnique_lowerRun_contains`](../Queens/LowerRunCoverage.lean#L46) | Every lower column belongs to exactly one enumerated run. |
| [`maximal_lower_run_iff`](../Queens/LowerRunCoverage.lean#L60) | **Corollary 19, enumeration correspondence.** Every maximal lower-column run is one of the canonical intervals used to define A275885, and conversely. |
| [`existsUnique_lowerRun_of_maximal`](../Queens/LowerRunCoverage.lean#L79) | The canonical indexing lists each maximal lower-column interval once. This makes the use of its ordered lengths in A275887 unambiguous. |
| [`lowerRunLength_range`](../Queens/LowerRunCoverage.lean#L89) | **Corollary 19, A275885 in sequence form:** the range of the canonical lower-run length sequence is exactly `{1, 2, 3}`. |

## `Queens/LowerRuns.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`nextUpperColumn`](../Queens/LowerRuns.lean#L46) | Corollary 19: the first upper column at or after `n`, counting the origin as upper. Its existence follows from the bound on lower-column runs. |
| [`nextLowerColumn`](../Queens/LowerRuns.lean#L52) | Corollary 19: the first lower column at or after `n`. Its existence follows from the bound on upper-column runs. |
| [`le_nextUpperColumn`](../Queens/LowerRuns.lean#L55) | For Corollary 19, the first upper column lies at or after the requested column. |
| [`nextUpperColumn_upper`](../Queens/LowerRuns.lean#L60) | For Corollary 19, the first upper column has the requested upper classification. |
| [`le_nextLowerColumn`](../Queens/LowerRuns.lean#L65) | For Corollary 19, the first lower column lies at or after the requested column. |
| [`nextLowerColumn_lower`](../Queens/LowerRuns.lean#L69) | For Corollary 19, the first lower column has the requested lower classification. |
| [`nextUpperColumn_le`](../Queens/LowerRuns.lean#L73) | For Corollary 19, minimality of the next upper column. |
| [`nextLowerColumn_le`](../Queens/LowerRuns.lean#L79) | For Corollary 19, minimality of the next lower column. |
| [`lower_before_nextUpperColumn`](../Queens/LowerRuns.lean#L83) | For Corollary 19, the columns before the next upper column are lower. |
| [`upper_before_nextLowerColumn`](../Queens/LowerRuns.lean#L91) | For Corollary 19, the columns before the next lower column are upper. |
| [`nextUpperColumn_le_add_three`](../Queens/LowerRuns.lean#L98) | Corollary 19: the next upper column occurs within three columns. |
| [`nextLowerColumn_le_add_five`](../Queens/LowerRuns.lean#L103) | Corollary 19: the next lower column occurs within five columns. |
| [`lowerRunStart`](../Queens/LowerRuns.lean#L109) | Corollary 19, A275885: the starting columns of successive lower runs, indexed from zero. Each next search begins at the preceding upper endpoint. |
| [`lowerRunEnd`](../Queens/LowerRuns.lean#L115) | Corollary 19, A275885: the upper column immediately after the `k`th lower run. The lower run occupies the half-open interval from start to end. |
| [`lowerRunLength`](../Queens/LowerRuns.lean#L118) | Corollary 19, A275885: the infinite sequence of lower-column run lengths. |
| [`lowerRunStart_lower`](../Queens/LowerRuns.lean#L121) | For Corollary 19, every lower-run start is a lower column. |
| [`lowerRunEnd_upper`](../Queens/LowerRuns.lean#L125) | For Corollary 19, every lower-run endpoint is an upper column. |
| [`lowerRunStart_lt_end`](../Queens/LowerRuns.lean#L129) | For Corollary 19, every enumerated lower run is nonempty. |
| [`lowerRunStart_add_length`](../Queens/LowerRuns.lean#L141) | Corollary 19: adding a lower run's length to its start gives the first following upper column. This is the endpoint identity used in path contraction. |
| [`lowerRunEnd_lt_start_succ`](../Queens/LowerRuns.lean#L146) | For Corollary 19, the upper block between consecutive lower runs is nonempty. |
| [`lowerRunStart_strictMono`](../Queens/LowerRuns.lean#L158) | For Corollary 19, the canonical run starts are strictly increasing. |
| [`lowerRunEnd_strictMono`](../Queens/LowerRuns.lean#L164) | For Corollary 19, the canonical run endpoints are strictly increasing. |
| [`lowerRunLength_bounds`](../Queens/LowerRuns.lean#L170) | Corollary 19: every term of A275885 is between one and three. |
| [`lower_in_run`](../Queens/LowerRuns.lean#L178) | For Corollary 19, the columns in an enumerated lower run are lower. |
| [`upper_between_runs`](../Queens/LowerRuns.lean#L182) | For Corollary 19, between consecutive lower runs all columns are upper. |
| [`upper_before_first_run`](../Queens/LowerRuns.lean#L187) | Corollary 19: the initial columns before the first lower run are upper. |
| [`lowerRun_maximal`](../Queens/LowerRuns.lean#L192) | Corollary 19: each interval in the canonical enumeration is a maximal lower-column run, with the correct left and right boundary conditions. |

## `Queens/Main.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`lowerDiagonal`](../Queens/Main.lean#L25) | Magnitude of the lower diagonal at zero-based chronological rank `k`. This is `dₖ₊₁` in Section 3, Lemma 5. |
| [`DiagonalDiscrepancy`](../Queens/Main.lean#L30) | The universal discrepancy hypothesis of Section 3, with the general constant of Proposition 8. Lemma 5 asserts `DiagonalDiscrepancy 4`. |
| [`lowerDiagonal_cast`](../Queens/Main.lean#L35) | Casting a lower-diagonal magnitude to the integers preserves subtraction because the corresponding queen is below the main diagonal. |
| [`lowerRowRank`](../Queens/Main.lean#L41) | The sorted rank of a chronological lower row. This supplies an explicit rearrangement for the sorting step in Section 3, Lemma 6. |
| [`sortedLowerRow_lowerRowRank`](../Queens/Main.lean#L46) | Sorting a chronological lower row at its rank recovers that row. |
| [`lowerRowRank_bijective`](../Queens/Main.lean#L54) | Chronological lower-row ranks give a permutation: both enumerations contain exactly the lower rows, and neither repeats a row. |
| [`lowerRowPermutation`](../Queens/Main.lean#L70) | The permutation matching chronological lower rows with sorted lower rows, used in Lemma 6. |
| [`sortedLowerRow_lowerRowPermutation`](../Queens/Main.lean#L74) | The chronological-to-sorted permutation preserves each lower-row value. |
| [`chronological_row_discrepancy`](../Queens/Main.lean#L80) | The rank-row identity turns diagonal discrepancy into chronological lower-row discrepancy, the first step of Section 3. |
| [`sorted_row_discrepancy`](../Queens/Main.lean#L88) | **Lemma 6, sorted-row bound.** Rearranging the chronological lower rows preserves their discrepancy from `U(xᴸⱼ)`. |
| [`lower_column_discrepancy`](../Queens/Main.lean#L101) | **Lemma 6, lower-column bound.** Combining the sorted-row estimate with Lemma 4 gives the column estimate used in the counting recurrence. |
| [`countDefect_le_of_diagonalDiscrepancy`](../Queens/Main.lean#L115) | **Lemma 7 for the greedy queens sequence.** The explicit input is the diagonal discrepancy bound; all counting and endpoint facts are proved. |
| [`upperCount_error_of_diagonalDiscrepancy`](../Queens/Main.lean#L134) | **Proposition 8, count estimate.** Diagonal discrepancy controls the distance of the actual greedy upper count from the golden-ratio slope. |
| [`position_bounds_of_diagonalDiscrepancy`](../Queens/Main.lean#L142) | **Proposition 8, queen positions.** For the actual greedy construction, the two golden-ratio bounds follow from the universal discrepancy bound. |
| [`main_of_diagonalDiscrepancy`](../Queens/Main.lean#L161) | **Theorem 1 from Lemma 5.** This separates the pure mathematical deduction from the finite verification. `Queens.main` in `Exactness` supplies the proved diagonal discrepancy and removes the hypothesis. |

## `Queens/Permutation.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`card_mul_pred_le_twice_sum`](../Queens/Permutation.lean#L22) | Distinct natural numbers have sum at least `0 + ⋯ + (card - 1)`, written without division. This is the counting estimate in Lemma 3. |
| [`range_mul_pred_le_twice_sum`](../Queens/Permutation.lean#L40) | The same coordinate-sum estimate for an injective enumeration, as used for both columns and rows in the proof of Lemma 3. |
| [`no_antidiagonal_tail`](../Queens/Permutation.lean#L49) | The occupied antidiagonals cannot contain a tail of the natural numbers. This is the coordinate-sum contradiction in Section 2, Lemma 3. |
| [`missing_row_forces_antidiagonal_tail`](../Queens/Permutation.lean#L78) | If a row is missing but all smaller rows are occupied, then all sufficiently large antidiagonals are occupied. This is the first half of the proof of Section 2, Lemma 3. |
| [`q_surjective`](../Queens/Permutation.lean#L117) | **Lemma 3 (surjectivity).** Every natural row contains a greedy queen. Together with `q_injective`, this says that `q` is a permutation of `ℕ`. |
| [`q_bijective`](../Queens/Permutation.lean#L127) | **Lemma 3 (permutation).** The greedy queens sequence is a bijection between the natural column indices and the natural row indices. |

## `Queens/RepeatedRunCoverage.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`existsUnique_repeated_lower_run_contains`](../Queens/RepeatedRunCoverage.lean#L18) | **Corollary 19, A275887 coverage:** every term of A275885 belongs to a unique finite maximal repetition of that value. Thus the exact range theorem for repeated run lengths describes the entire sequence of repetitions. |

## `Queens/RepeatedRuns.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`lowerRuns_fortyRunEdge`](../Queens/RepeatedRuns.lean#L35) | Appendix A: consecutive actual lower runs give a run-graph edge whenever the first upper endpoint is covered by the forty-symbol state path. |
| [`lowerRunLength_follows_runGraph`](../Queens/RepeatedRuns.lean#L81) | Appendix A: the A275885 terms beginning with term 24 (zero-based index 23) are the labels of an actual walk in the certified run graph. |
| [`no_twelve_equal_lower_run_lengths`](../Queens/RepeatedRuns.lean#L100) | Corollary 19: twelve consecutive terms of A275885 cannot all be equal. This excludes infinite constant tails as well as overly long finite repetitions. |
| [`early_repeated_lower_run_length`](../Queens/RepeatedRuns.lean#L130) | Corollary 19: maximal repetitions whose start precedes the graph's safe left boundary have an allowed length, by the checked actual-prefix table. |
| [`repeated_lower_run_length_bound`](../Queens/RepeatedRuns.lean#L154) | Corollary 19: every maximal run of equal lower-run lengths belongs to `{1,…,9,11}`. In particular a maximal run of exactly ten equal terms is impossible. |
| [`repeated_lower_run_lengths`](../Queens/RepeatedRuns.lean#L169) | **Corollary 19, A275887:** the lengths of maximal runs of equal terms in the lower-column run sequence are exactly `{1,…,9,11}`. |
| [`no_ten_repeated_lower_runs`](../Queens/RepeatedRuns.lean#L184) | **Corollary 19:** ten never occurs as the length of a maximal run of equal terms in A275885, although eleven does occur. |

## `Queens/RowCounts.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`upperRowSources`](../Queens/RowCounts.lean#L18) | The source columns of upper queens whose rows are at most `T`. Their cardinality is the upper-row count `B(T)` in Section 4.4. |
| [`upperRowCount`](../Queens/RowCounts.lean#L23) | The upper-row count `B(T)` in Proposition 13. Distinct sources occupy distinct rows by the nonattacking condition. |
| [`mem_upperRowSources`](../Queens/RowCounts.lean#L27) | Membership in the upper-row source set, without the redundant column bound. This is the finite counting interpretation of `B(T)` in Proposition 13. |
| [`upperRowSources_mono`](../Queens/RowCounts.lean#L34) | Upper-row source sets increase with the threshold, as used when taking the difference `B(n) - B(n - 1)` in Section 4.4. |
| [`upperRowCount_eq_adjustment`](../Queens/RowCounts.lean#L51) | **Proposition 13 (upper-row count)**, expressed using absolute retained columns `[a,b)`. Relative offsets turn the two cardinalities into `J(T-m-κ)`. The old- and future-source hypotheses are exactly the two exclusions required by the paper's proposition. |
| [`upperRowCount_eq_previous_add_bit`](../Queens/RowCounts.lean#L96) | Increasing a positive row threshold adds precisely the upper queen in that row, if there is one. This is `bₙ = B(n) - B(n - 1)` in Section 4.4. |
| [`upperRowBit_eq_count_difference`](../Queens/RowCounts.lean#L131) | The output row bit is the signed difference between consecutive upper-row counts, the final identity in Proposition 13. |

## `Queens/Runs.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`MaximalRun`](../Queens/Runs.lean#L15) | Corollary 19: a nonempty maximal run of a predicate, specified by its first index and length. The left boundary is omitted only at index zero. |
| [`MaximalRun.mem`](../Queens/Runs.lean#L26) | For Corollary 19, a finite maximal-run assertion is decidable when its predicate is decidable. -/ instance {p : ℕ → Prop} [DecidablePred p] (start length : ℕ) : Decidable (MaximalRun p start length) := inferInstanceAs (Decidable (_ ∧ _)) /-- Every index inside a maximal run satisfies its predicate. This interval interface avoids arithmetic on `Fin` indices in Corollary 19's coverage proofs. |
| [`MaximalRun.first`](../Queens/Runs.lean#L34) | The first term of a maximal run satisfies its predicate. In Corollary 19, this identifies the repeated value from the first lower-run length. |
| [`ConsecutiveGap`](../Queens/Runs.lean#L40) | Corollary 19: two consecutive occurrences of a predicate, specified by the first occurrence and their positive difference. |
| [`MaximalRun.length_le`](../Queens/Runs.lean#L50) | For Corollary 19, a finite consecutive-gap assertion is decidable for a decidable predicate. -/ instance {p : ℕ → Prop} [DecidablePred p] (start gap : ℕ) : Decidable (ConsecutiveGap p start gap) := inferInstanceAs (Decidable (_ ∧ _)) /-- Corollary 19: forbidding a constant block of length `bound + 1` bounds every maximal run by `bound`. |
| [`ConsecutiveGap.length_le`](../Queens/Runs.lean#L60) | Corollary 19: a gap contains one fewer consecutive failures of the predicate. A forbidden complementary block therefore bounds the gap. |
| [`maximalRun_congr`](../Queens/Runs.lean#L72) | For Corollary 19, maximal-run assertions only depend on the predicate up to their right boundary. This transfers computed occurrence witnesses to an infinite sequence. |
| [`consecutiveGap_congr`](../Queens/Runs.lean#L85) | For Corollary 19, consecutive-gap assertions only depend on the predicate up to their second endpoint. This transfers a computed gap to the infinite sequence. |
| [`MaximalRun.length_unique`](../Queens/Runs.lean#L98) | For Corollary 19, two maximal runs of the same predicate with the same start have the same length: the shorter right boundary would otherwise lie inside the longer run. |
| [`MaximalRun.shift`](../Queens/Runs.lean#L108) | For Corollary 19, dropping an initial prefix preserves every maximal run that starts at or after the cut. A run starting exactly at the cut becomes an initial run. |

## `Queens/RunsAndGaps.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`IsUpperColumnWithOrigin`](../Queens/RunsAndGaps.lean#L18) | Corollary 19: upper-column membership with the origin included, as required by A275886 and A275888. Away from zero this is the usual strict upper condition. |
| [`not_upperColumnWithOrigin_iff`](../Queens/RunsAndGaps.lean#L22) | Corollary 19: lower columns are exactly the complement of upper columns when the origin is counted as upper. |
| [`queenWord_history_vertex`](../Queens/RunsAndGaps.lean#L33) | Section 6.4 applied to an arbitrary positive starting column: every consecutive twelve-symbol block of the actual word is a history vertex. |
| [`no_four_lower_columns`](../Queens/RunsAndGaps.lean#L62) | Corollary 19: four consecutive lower columns never occur. The origin is handled directly; every positive-index block lies in a certified history. |
| [`no_six_upper_columns`](../Queens/RunsAndGaps.lean#L79) | Corollary 19: six consecutive upper columns never occur, including a possible run starting at the origin. |
| [`lower_column_run_lengths`](../Queens/RunsAndGaps.lean#L105) | **Corollary 19, A275885:** the lengths of maximal lower-column runs are exactly 1, 2, and 3. Each permitted length is attained by actual greedy queens. |
| [`upper_column_run_lengths`](../Queens/RunsAndGaps.lean#L121) | **Corollary 19, A275886:** counting the origin as upper, the lengths of maximal upper-column runs are exactly 1 through 5. |
| [`upper_column_gaps`](../Queens/RunsAndGaps.lean#L137) | **Corollary 19, A275888:** counting the origin as upper, the gaps between consecutive upper columns are exactly 1 through 4. |
| [`lower_column_gaps`](../Queens/RunsAndGaps.lean#L157) | **Corollary 19, A275889:** the gaps between consecutive lower columns are exactly 1 through 6. |

## `Queens/RunsCoverage.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`MaximalRun.eq_of_contains`](../Queens/RunsCoverage.lean#L17) | Two maximal runs containing the same index are the same interval. This is the uniqueness needed when interpreting the run sequences of Corollary 19. |
| [`existsUnique_maximalRun_contains`](../Queens/RunsCoverage.lean#L34) | If arbitrarily placed blocks of a fixed length cannot all satisfy a predicate, every occurrence lies in a unique finite maximal run. Applied to Corollary 19, this excludes an infinite final run from the sequence interpretation. |

## `Queens/SharpAnalysis.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`seedUpperCount`](../Queens/SharpAnalysis.lean#L21) | The upper count read from the verified seed table. This is used only to establish Proposition 21's initial inequalities. |
| [`upperCount_eq_seedUpperCount`](../Queens/SharpAnalysis.lean#L26) | In the first thirty columns the seed upper count equals the actual upper count, by the greedy-prefix identification in Section 6.1. |
| [`prefix_sharp_count_error`](../Queens/SharpAnalysis.lean#L41) | Proposition 21's base cases, proved by exact integer computation and rational bounds on the golden ratio. The proof uses kernel reduction only. |

## `Queens/SharpRecords.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`sharp_record_bounds`](../Queens/SharpRecords.lean#L19) | Proposition 21, record inequality: every actual state from column 30 onwards has `-4 ≤ w - \|D\| - φ \|R\| ≤ 1`. |
| [`seed_lower_discrepancy_le_two`](../Queens/SharpRecords.lean#L30) | Proposition 21, finite starting check: every lower queen before column 30 has upper diagonal discrepancy at most two. This check uses the Lean kernel. |
| [`prefix_lower_discrepancy_le_two`](../Queens/SharpRecords.lean#L38) | Proposition 21, direct starting case: the checked upper discrepancy bound holds for every actual lower queen before column 30. |
| [`sharp_lower_choice_bound`](../Queens/SharpRecords.lean#L51) | Proposition 21, local lower-choice inequality: the actual chosen offset obeys `w - r - \|D\| ≤ 2` from column 30 onwards. |
| [`lower_diagonal_discrepancy_le_two`](../Queens/SharpRecords.lean#L71) | Proposition 21: the chronological lower diagonal of positive rank `k+1` exceeds that rank by at most two. This sharpens the upper half of Lemma 5. |

## `Queens/SharperBounds.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`sharp_count_error`](../Queens/SharperBounds.lean#L20) | **Proposition 21, upper-count error.** The actual upper count lies strictly between `n / φ - 3 / φ` and `n / φ + 2 / φ`, including at the origin. |
| [`upper_position_error_eq_countError`](../Queens/SharperBounds.lean#L34) | Section 6.6: at an upper column the position error is exactly the upper-count error, using Lemma 2's upper-row formula. |
| [`countError_succ`](../Queens/SharperBounds.lean#L40) | Section 6.6: the error increment distinguishes upper and lower columns. The origin is excluded because it is neither an upper nor a lower queen. |
| [`sharp_upper_position`](../Queens/SharperBounds.lean#L48) | **Proposition 21, upper queens.** Using the upper-column increment sharpens the lower endpoint beyond the uniform count estimate. |
| [`sharp_lower_row_count`](../Queens/SharperBounds.lean#L64) | Section 6.6: at every lower queen the error of the row relative to the upper count is between `-2` and `4`, by the two diagonal-discrepancy bounds. |
| [`sharp_lower_position`](../Queens/SharperBounds.lean#L79) | **Proposition 21, lower queens.** The lower-column increment and the asymmetric diagonal estimates give the sharper two-sided row bounds. |
| [`sharper_bounds`](../Queens/SharperBounds.lean#L96) | **Proposition 21 (sharper constants).** Both branches of the greedy queen permutation satisfy the paper's strict asymmetric golden-ratio bounds. The two implications also hold vacuously at the origin. |

## `Queens/Sorting.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`exists_le_map_ge`](../Queens/Sorting.lean#L24) | An injection of natural numbers sends some element of the first `n + 1` indices to an index at least `n`. This is the finite pigeonhole argument used in Lemma 6. |
| [`exists_ge_perm_le`](../Queens/Sorting.lean#L37) | A permutation has an index at least `n` whose image is at most `n`. This is the reverse pigeonhole argument in Lemma 6. |
| [`abs_sub_le_of_monotone_rearrangement`](../Queens/Sorting.lean#L46) | **Lemma 6, sorting step**, in an ordered additive group. If the chronological sequence `v ∘ e` stays within `C` of the monotone reference sequence `t`, the monotone enumeration `v` satisfies the same bound. In the paper, `v` is the sequence of sorted lower rows and `t j = xⱼᴸ - j`; `e` matches chronological rows with their sorted ranks. |

## `Queens/Word.lean`

| Declaration | Purpose and paper correspondence |
|---|---|
| [`columnBit`](../Queens/Word.lean#L14) | Definition 9: `uₙ`, the indicator of an upper queen in column `n`. |
| [`upperRowBit`](../Queens/Word.lean#L18) | Definition 9: `bₙ`, the indicator of an upper queen in row `n`. An upper queen in row `n` must occur before column `n`, so the test is finite. |
| [`queenSymbol`](../Queens/Word.lean#L23) | Definition 9: the actual symbol `σₙ = 2uₙ + bₙ`. The paper uses positive indices; the harmless extension at zero is also defined. |
| [`columnBit_le_one`](../Queens/Word.lean#L26) | Definition 9: the column indicator is a bit. |
| [`upperRowBit_le_one`](../Queens/Word.lean#L31) | Definition 9: the row indicator is a bit. |
| [`queenSymbol_lt_four`](../Queens/Word.lean#L36) | Definition 9: the queen word takes values in the four-symbol alphabet. |
| [`upperRowBit_eq_one_iff`](../Queens/Word.lean#L43) | Definition 9: a row bit is one exactly when an upper queen occupies that row. |
