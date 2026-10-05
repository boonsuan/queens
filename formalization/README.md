# Greedy Queens and the Golden Ratio

This directory formalizes Boon Suan Ho's *Greedy Queens and the Golden Ratio*
in Lean 4 with mathlib. It is a self-contained Lake project within the
[companion-code repository](../README.md).

**Paper:** [Greedy Queens and the Golden Ratio](https://arxiv.org/abs/2609.31336) (arXiv:2609.31336).

The formalization proves Theorems 1 and 2 for the sequence defined by the greedy
placement rule, together with every numbered result of Sections 2–6 that supports
them, and Corollaries 19 and 20. All proofs, including the finite computations,
are checked by the Lean kernel. There are no `sorry`s, custom axioms, or
native-evaluation axioms.

## Where to start

- **Read the results:** [the main theorems](#the-main-theorems) below state
  Theorems 1 and 2 directly in Lean.
- **Follow the proof:** the [paper-to-code table](#paper-to-code-correspondence)
  follows the paper section by section; the [declaration index](docs/DECLARATIONS.md)
  records the purpose and paper correspondence of individual definitions and results.
- **Check the formalization:** follow [Build and check](#build-and-check).
  [`Queens.lean`](Queens.lean) imports the complete formalized result set.
- **Inspect the finite verification:** read the [verification design](docs/KERNEL_VERIFICATION.md)
  and the [axiom audit](docs/AXIOMS.txt). The certificates are generated from the
  reference programs in [`verification/`](../verification/) and [`oeis/`](../oeis/).

## The main theorems

Place one queen in each column $n = 0, 1, 2, \ldots$ of the nonnegative quadrant,
always choosing the least row not attacked by an earlier queen. Write $q_n$ for
its row and $\varphi = (1 + \sqrt{5})/2$. Theorem 1 says that the queens remain
within fixed distances of the lines $y = \varphi x$ and $y = x/\varphi$.

Here is the complete statement and final proof from
[`Queens/Exactness.lean`](Queens/Exactness.lean), inside `namespace Queens`:

```lean
theorem main (n : ℕ) :
    (n < q n → |(q n : ℝ) - (n : ℝ) * Real.goldenRatio| < 5 / Real.goldenRatio) ∧
    (q n < n → |(q n : ℝ) - (n : ℝ) / Real.goldenRatio| < 4 + 5 / Real.goldenRatio) :=
  main_of_diagonalDiscrepancy bounded_diagonal_discrepancy n
```

The first implication concerns upper queens, with `n < q n`; the second concerns
lower queens, with `q n < n`. The casts `(: ℝ)` express the bounds in the real
numbers, and `Real.goldenRatio` is mathlib's golden ratio. The origin has `q 0 = 0`
and satisfies both implications vacuously; every other queen lies strictly above
or below the main diagonal.

[`bounded_diagonal_discrepancy`](Queens/Exactness.lean) is the proved Lemma 6.
[`main_of_diagonalDiscrepancy`](Queens/Main.lean) separates the mathematical
deduction from that lemma from the finite computation used to establish it.
The final theorem above has no unproved discrepancy or finite-state hypothesis.

Theorem 2 sharpens the constants to those of the ranges that Knuth observed
computationally. From [`Queens/KnuthRanges.lean`](Queens/KnuthRanges.lean):

```lean
theorem knuth_bounds (n : ℕ) :
    (n < q n → (19 * Real.sqrt 5 - 49) / 8 < (q n : ℝ) - n * Real.goldenRatio ∧
      (q n : ℝ) - n * Real.goldenRatio < Real.sqrt 5 - 1) ∧
    (q n < n → 15 - 8 * Real.sqrt 5 < (q n : ℝ) - n / Real.goldenRatio ∧
      (q n : ℝ) - n / Real.goldenRatio < 13 - 4 * Real.sqrt 5)
```

In Knuth's 1-indexed coordinates, the queen in column $c = n + 1$ lies on row
$s(c) = q_n + 1$, written `knuthRow c`. The consequence stated in Theorem 2 is:

```lean
theorem knuth_ranges {c : ℕ} (hc : 1 ≤ c) :
    (knuthRow c : ℝ) ∈ Set.Icc (c / Real.goldenRatio - 3) (c / Real.goldenRatio + 5) ∪
      Set.Icc (c * Real.goldenRatio - 2) (c * Real.goldenRatio + 1)
```

Since `knuthRow c` is an integer, membership in these real intervals is
membership in the paper's integer intervals.

## The greedy definition

[`Queens/Greedy.lean`](Queens/Greedy.lean) starts with the placement rule itself.
These excerpts are also inside `namespace Queens`:

```lean
def Available (n r : ℕ) (previous : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, r ≠ previous i ∧ r + i.val ≠ previous i + n ∧
    r + n ≠ previous i + i.val
```

`Fin n` indexes the earlier columns `0, …, n − 1`. The three inequalities exclude
attacks along rows, diagonals, and antidiagonals, as in equation (1). The lemma
`exists_available` proves that an available row always exists, so the sequence is
defined by:

```lean
noncomputable def q (n : ℕ) : ℕ :=
  Nat.find (exists_available n (fun i => q i.val))
termination_by n
```

`Nat.find` chooses the least row satisfying the predicate; recursion only refers
to earlier columns. The theorems `q_available` and `q_le_of_available` express
availability and minimality. [`q_bijective`](Queens/Permutation.lean) proves
Lemma 4: every nonnegative row is eventually used exactly once.

The mathematical definition is marked `noncomputable`. Numerical witnesses are
handled by separate, proved finite-prefix checkers ([`Finite/Seed`](Queens/Finite/Seed.lean),
[`Finite/FirstColumns`](Queens/Finite/FirstColumns.lean), and
[`Finite/GreedyPrefix`](Queens/Finite/GreedyPrefix.lean)), which identify every
accepted row with this same `q`.

## Formalized scope

For the actual greedy sequence, the project proves:

- **Theorem 1** and everything it rests on: Lemmas 3–8, Proposition 9,
  Definitions 10–12 and 15, Propositions 13–14, Condition 16, Lemma 17, and
  Proposition 18 with its finite verification.
- **Theorem 2** and the rest of Section 6.6: the asymmetric bound
  $-4 \le d_j - j \le 2$ and the lower queens attaining both ends, Lemma 21 (one-step error identity), the link
  $H_{\mathrm{in}}(S_n) = H_{\mathrm{out}}(S_m)$ of equation (27), Definition 22
  (consistent window bounds), Lemma 23 (window bounds hold on the board),
  Proposition 24 (finite verification of the window bounds), and Knuth's ranges
  in 1-indexed coordinates.
- **Corollary 19 (diagonal coverage):** [`q_diagonal_bijective`](Queens/DiagonalCoverage.lean)
  proves that every signed diagonal contains exactly one queen.
- **Corollary 20 (column runs and gaps):** all five range assertions, including both
  exclusion of other values and occurrence of every listed value in the actual
  greedy sequence.
- Statements made in the text: every vertex of the history graph has an outgoing
  edge (Section 6.2); for every state of the state graph, every twelve consecutive
  symbols of $H_{\mathrm{in}}Q$ form a vertex, and so does $H_{\mathrm{out}}$
  (Section 4.3); and every vertex is the output history of some state (Section 6.6).

Corollary 20 gives the following exact ranges:

| Quantity | Range |
|---|---|
| Lengths of maximal lower-column runs | `{1, 2, 3}` |
| Lengths of maximal upper-column runs | `{1, …, 5}` |
| Gaps between consecutive upper columns | `{1, …, 4}` |
| Gaps between consecutive lower columns | `{1, …, 6}` |
| Lengths of maximal repetitions in the lower-run length sequence | `{1, …, 9, 11}` |

For these run and gap statements, the origin is included among upper columns,
as in the paper. [`LowerRunCoverage`](Queens/LowerRunCoverage.lean) proves that
the canonical enumeration lists every maximal lower run exactly once.
[`RepeatedRunCoverage`](Queens/RepeatedRunCoverage.lean) proves that each term of
the lower-run length sequence belongs to a unique finite repetition, excluding
an infinite constant tail.

**Outside the formalized scope:**

- Section 7 (fast generation with little memory): the generator and its table,
  Proposition 25 (sequential generation), the measured performance, and the table
  of states in Section 7.5.
- The unnumbered catalogue of return words after Corollary 20, which the
  companion's `oeis/` programs check.
- Unnumbered computational observations: the history-length experiment of
  Appendix A2 and the scan of the first $10^{11}$ columns quoted after the proof
  of Theorem 2.
- The unnumbered remarks on the game interpretation (Section 1), on 1-indexed
  coordinates for general `C` (Section 3), and on Sprague–Grundy values on
  diagonals (Section 6.4).

Result numbers refer to the [paper](https://arxiv.org/abs/2609.31336).

## Paper-to-code correspondence

The proof has three parts. Sections 2–3 deduce the golden-ratio estimates from
bounded diagonal discrepancy. Sections 4–5 prove that finite local records retain
the actual greedy step. Section 6 checks a closed finite invariant, follows the
actual board indefinitely to establish the discrepancy bound, and then bounds the
counting error by window bounds on the history graph to prove Theorem 2. Module
introductions and declaration docstrings explain the correspondence in more detail.

| Paper | Lean module | Main declarations |
|---|---|---|
| §1, equation (1) | [`Greedy`](Queens/Greedy.lean) | `Available`, `q`, `q_available`, `q_le_of_available` |
| §1, Theorem 1 | [`Exactness`](Queens/Exactness.lean) | `main` |
| §1, Theorem 2 | [`KnuthRanges`](Queens/KnuthRanges.lean) | `knuth_bounds`, `knuthRow`, `knuth_ranges` |
| §2, Lemma 3 (upper queens) | [`Greedy`](Queens/Greedy.lean) | `q_eq_add_upperCount` |
| §2, Lemma 4 (permutation) | [`Permutation`](Queens/Permutation.lean) | `no_antidiagonal_tail`, `q_surjective`, `q_bijective` |
| §2, equations (2)–(3) | [`Greedy`](Queens/Greedy.lean), [`LowerColumns`](Queens/LowerColumns.lean), [`Main`](Queens/Main.lean) | `upperCount`, `lowerCount`, `lowerColumn`, `lowerDiagonal` |
| §2, Lemma 5 (sorted lower rows) | [`LowerRows`](Queens/LowerRows.lean) | `sortedLowerRow`, `sortedLowerRow_eq` |
| §3, Lemma 6 (bounded diagonal discrepancy) | [`Main`](Queens/Main.lean), [`Exactness`](Queens/Exactness.lean) | `DiagonalDiscrepancy`, `bounded_diagonal_discrepancy` |
| §3, equation (6), Lemma 7 (sorting) | [`LowerColumns`](Queens/LowerColumns.lean), [`Sorting`](Queens/Sorting.lean), [`Main`](Queens/Main.lean) | `lowerCount_lowerColumn`, `abs_sub_le_of_monotone_rearrangement`, `lower_column_discrepancy` |
| §3, Lemma 8 (counting recurrence) | [`Counting`](Queens/Counting.lean) | `counting_recurrence_int`, `counting_recurrence` |
| §3, Proposition 9 (contraction and queen positions); proof of Theorem 1 | [`GoldenRatio`](Queens/GoldenRatio.lean), [`Main`](Queens/Main.lean) | `count_error_lt`, `position_bounds_of_diagonalDiscrepancy`, `main_of_diagonalDiscrepancy` |
| §4.1, equations (11)–(13) | [`LocalBoard`](Queens/LocalBoard.lean), [`LocalCandidates`](Queens/LocalCandidates.lean) | `rowReference`, `diagonalReference`, `window`, `rowOffsets`, `local_rank_identity`, `available_candidate_iff` |
| §4.2, Definitions 10–11 (queen word, local state) | [`Word`](Queens/Word.lean), [`Finite/Local`](Queens/Finite/Local.lean), [`LocalRepresentation`](Queens/LocalRepresentation.lean) | `queenSymbol`, `Finite.State`, `RecordsRepresented`, `StateRepresented` |
| §4.3, Definition 12 (history graph) | [`Finite/HistoryCore`](Queens/Finite/HistoryCore.lean), [`Finite/HistoryChecking`](Queens/Finite/HistoryChecking.lean), [`Finite/Encoding`](Queens/Finite/Encoding.lean), [`LocalRequests`](Queens/LocalRequests.lean) | `historyWindow`, `HistoryGraph.FollowsThrough`, `HistoryGraph.WellFormed`, `destination` |
| §4.4, Propositions 13–14 | [`LocalGeometry`](Queens/LocalGeometry.lean), [`RowCounts`](Queens/RowCounts.lean), [`LocalSources`](Queens/LocalSources.lean), [`Finite/Sources`](Queens/Finite/Sources.lean) | relative source geometry, row-count adjustment, exact executable tests |
| §4.5, Algorithm 1, equations (22)–(23), Definition 15 (state graph) | [`Finite/Local`](Queens/Finite/Local.lean), [`LocalUpdates`](Queens/LocalUpdates.lean), [`Finite/UpdateSemantics`](Queens/Finite/UpdateSemantics.lean), [`Finite/Certificate`](Queens/Finite/Certificate.lean) | `calculate`, `updateState`, `Finite.Step` |
| §5, Condition 16 (bounds on the stored records) | [`Finite/Local`](Queens/Finite/Local.lean) | `Finite.Condition` |
| §5, Lemma 17 (the records determine the actual step) | [`LocalChoice`](Queens/LocalChoice.lean), [`LocalAdvances`](Queens/LocalAdvances.lean), [`LocalBounds`](Queens/LocalBounds.lean), [`Finite/Branching`](Queens/Finite/Branching.lean), [`Finite/FinishSemantics`](Queens/Finite/FinishSemantics.lean), [`GeneralExactness`](Queens/GeneralExactness.lean), [`Exactness`](Queens/Exactness.lean) | `chooseFrom_contains_actual`, `allBranches_branch`, `finishChoice_contains_actual`, `local_step_exact` |
| §6.1, the starting board | [`Finite/PrefixTransfer`](Queens/Finite/PrefixTransfer.lean), [`Finite/Seed`](Queens/Finite/Seed.lean) | `q_eq_seedRow`, `initialState_represented`, `queenWord_follows_through_twentyNine` |
| §6.2, the history graph | [`Finite/History`](Queens/Finite/History.lean) | `historyGraph_wellFormed`, `historyGraph_vertex_count`, `historyGraph_edge_count`, `historyGraph_no_sinks` |
| §6.3, Proposition 18 (finite verification) | [`Finite/Certificate`](Queens/Finite/Certificate.lean), [`Finite/Reachability`](Queens/Finite/Reachability.lean) | `certificate_checked`, `certified_successors`, `certified_iff_reachable`, `reached_state_count`, `reached_edge_count` |
| §6.4, proof of Lemma 6 | [`Identification`](Queens/Identification.lean), [`Exactness`](Queens/Exactness.lean) | `actualInvariant_of_localStepExact`, `bounded_diagonal_discrepancy` |
| §6.4, Corollary 19 (diagonal coverage) | [`DiagonalCoverage`](Queens/DiagonalCoverage.lean) | `q_diagonal_bijective`, `existsUnique_queen_on_diagonal`, `lowerDiagonal_bijOn` |
| §6.5, Corollary 20 (column runs and gaps): runs and gaps | [`RunsAndGaps`](Queens/RunsAndGaps.lean), [`Finite/RunWitnesses`](Queens/Finite/RunWitnesses.lean), [`Finite/LowerRunWitnesses`](Queens/Finite/LowerRunWitnesses.lean) | `lower_column_run_lengths`, `upper_column_run_lengths`, `upper_column_gaps`, `lower_column_gaps` |
| §6.5, Corollary 20: the lower-run sequence | [`LowerRuns`](Queens/LowerRuns.lean), [`LowerRunCoverage`](Queens/LowerRunCoverage.lean) | `lowerRunLength`, `existsUnique_lowerRun_of_maximal`, `lowerRunLength_range` |
| §6.5, Corollary 20: repeated run lengths | [`LabeledRuns`](Queens/LabeledRuns.lean), [`RepeatedRuns`](Queens/RepeatedRuns.lean), [`RunsCoverage`](Queens/RunsCoverage.lean), [`RepeatedRunCoverage`](Queens/RepeatedRunCoverage.lean) | `RunLengthCertificate`, `repeated_lower_run_lengths`, `no_ten_repeated_lower_runs`, `no_twelve_equal_lower_run_lengths`, `existsUnique_repeated_lower_run_contains` |
| §6.6, $-4 \le d_j - j \le 2$ | [`KnuthRanges`](Queens/KnuthRanges.lean) | `lowerDiagonal_sub_rank_le_two`, `diagonal_discrepancy_range`, `diagonal_discrepancy_range_attained` |
| §6.6, Lemma 21 (one-step error identity) | [`ErrorIdentity`](Queens/ErrorIdentity.lean) | `upperCount_eq_reference_window`, `one_step_error_identity` |
| §6.6, equation (27), Definition 22 (consistent window bounds), Lemma 23 (window bounds hold on the board) | [`WindowBounds`](Queens/WindowBounds.lean) | `input_eq_output_of_represented`, `ConsistentWindowBounds`, `window_bounds_hold` |
| §6.6, Proposition 24 (finite verification of the window bounds) | [`SqrtFive`](Queens/SqrtFive.lean), [`Finite/WindowChecks`](Queens/Finite/WindowChecks.lean), [`Finite/WindowCertificate`](Queens/Finite/WindowCertificate.lean), [`KnuthRanges`](Queens/KnuthRanges.lean) | `sqrtFiveEval_le`, `certified_windowConsistent`, `certified_lowerChoice_bounds`, `upper_window_bounds`, `window_bounds_start`, `window_bounds_verified` |
| §6.6, proof of Theorem 2 | [`Finite/FirstColumns`](Queens/Finite/FirstColumns.lean), [`KnuthRanges`](Queens/KnuthRanges.lean) | `first_upper_position_bounds`, `upper_position_bounds`, `lower_position_bounds`, `knuth_bounds`, `knuth_ranges` |
| Appendix A3, the refined certificate | [`GeneralExactness`](Queens/GeneralExactness.lean), [`Finite/FortyCertificate`](Queens/Finite/FortyCertificate.lean), [`Finite/FortySeed`](Queens/Finite/FortySeed.lean), [`FortyPath`](Queens/FortyPath.lean) | `local_step_exact_of_memory`, checked closed invariant, `actualVertex_represents`, `actualVertex_step` |
| Appendix A3, graphs for the gap and run sequences | [`Finite/PathContraction`](Queens/Finite/PathContraction.lean), [`Finite/RepeatedRunCertificate`](Queens/Finite/RepeatedRunCertificate.lean) | `runTargets_mem`, `repeatedRunCertificate` |

The paper indexes lower queens and sorted lower rows starting at one. Lean uses
zero-based indices: `lowerColumn k`, `lowerDiagonal k`, and `sortedLowerRow k`
correspond to the paper's rank `k + 1`. Board columns and rows are zero-based in both.
Signed differences are taken in `ℤ` or `ℝ`, avoiding truncated natural subtraction.
The golden ratio is mathlib's `Real.goldenRatio = (1 + √5) / 2`. History-graph
vertices are twelve-symbol words encoded in base four, so the window bounds
`lo` and `hi` of Section 6.6 are functions on natural numbers; only their values
at vertices matter.

## Build and check

The project pins Lean `v4.34.1` and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` (mathlib's `v4.34.1` release);
transitive dependencies are pinned in `lake-manifest.json`.

With [elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
cd formalization
lake exe cache get
python3 scripts/build_kernel.py
lake build --wfail
lake lint -- --no-build
python3 scripts/check_axioms.py
python3 scripts/declaration_index.py
```

`elan` selects the pinned Lean version, and `lake exe cache get` downloads
precompiled mathlib dependencies. `--wfail` makes build warnings fail the check.

The build script stages the large certificates to control simultaneous memory
use. Its optional `--parallel-forty` flag checks the four largest independent
parts together. On a 10-core Apple-silicon machine with 24 GiB of
memory, a cold build takes about 37 minutes with the default staging and about
20 minutes with `--parallel-forty`; the four parallel parts use about 10 GiB, and
the repeated-run check about 9 GiB on its own. See the [build details](docs/KERNEL_VERIFICATION.md).
Completed proofs are cached by Lake. After the first build, `lake build --wfail`
is sufficient for incremental checks.

The certificate exporters read the reference programs and the history graph
from the repository's [`verification/`](../verification/) and [`oeis/`](../oeis/)
folders. Continuous integration regenerates every certificate and checks that
the result is unchanged.

For interactive reading, open this directory in an editor with Lean 4 support.

`Queens.lean` is the library entry point. Public mathematical definitions and results carry
docstrings; module introductions explain the paper correspondence and indexing choices.
The [declaration index](docs/DECLARATIONS.md) lists these named source declarations
and their docstrings; instances, structure fields, and generated auxiliary declarations
are not separate index entries.

Ordinary builds enable mathlib's standard source linters. `lake lint` additionally
checks declarations throughout the imported `Queens` library. The source-lint
exceptions are the downstream copyright-header convention and documented line/file
length allowances for generated certificates. Evaluation budgets are scoped to
the finite checks that need them.

### Continuous integration

Two workflows run on pull requests to `main` and pushes to `main`; both can also
be run manually from GitHub's Actions tab.

- The [certificate workflow](../.github/workflows/certificates.yml) regenerates
  the certificates from the reference programs and checks that they match the
  committed files. It needs only Python and takes about a minute, and it runs
  whenever `verification/**`, `oeis/**` or `formalization/**` changes, so the
  certificates cannot drift from the programs they come from.
- The [Lean workflow](../.github/workflows/formalization.yml) builds the proofs
  with warnings treated as errors, runs the declaration linters and kernel-only
  axiom audit, and checks the declaration documentation. It runs only when
  `formalization/**` changes. It uses the pinned toolchain and dependencies,
  stages the large kernel checks, and caches successful builds for incremental
  checking.

## Finite verification and trust

The history graph has **2,092 vertices and 2,603 labeled edges**, and every vertex
has an outgoing edge. The state graph has **7,014 distinct states**, whose recomputed
successor sets have **8,327 directed edges**. Each state satisfies Condition 16, every
calculation succeeds, and every successor belongs to the same table. These statements
are checked by Lean. A separate checked predecessor certificate proves that every
listed state is reachable, so the table is exactly the state graph of Definition 15,
not merely a closed superset.

Computational proofs use `decide +kernel` and ordinary checker-soundness
lemmas. Balanced lookup trees and bounded certificate pieces make these checks
practical without adding compiler-evaluation axioms. `AxiomAudit.lean` prints
the dependencies of the principal results and inspects every imported project
declaration, including private helpers. `scripts/check_axioms.py` rejects
anything beyond `propext`, `Classical.choice`, and `Quot.sound`.

**Window bounds.** The certificate for Proposition 24 proposes, for each of the
2,092 vertices, the exact values `8 lo(W)` and `8 hi(W)` in `ℤ[√5]` and the index
of a state whose output history is `W`. Lean compares elements of `ℤ[√5]` with
mathlib's decidable order and transfers each comparison to `ℝ` by a proved monotone
evaluation map. At each of the 7,014 states, Lean recomputes the choices of every
branch and checks both inequalities of Definition 22, property (ii) at every lower
choice, and `w - r - |D| ≤ 2`. At each vertex it checks property (i) when the last
column bit is 1, and that the witness state has that output history. It also
checks the hypothesis of Lemma 23 for `30 ≤ n ≤ 48` and the bounds of Theorem 2
for `1 ≤ n ≤ 48`, using a proved table of the first 49 rows.
On the machine above, the window-bound stage takes about a minute.

Corollary 20 additionally uses a forty-symbol history graph, an indexed actual-state
path, proved path contractions, and independently verified greedy-prefix witnesses
for attainment. The forty-symbol invariant has 29,267 indexed entries and 30,000
indexed edges; its history graph has 16,876 entries and 17,499 labeled edges. For
this refinement the proof establishes a closed invariant containing the actual
path. It does not require a separate exact-reachability or distinct-state count
theorem.

The Python exporters supply only candidate data and witnesses. Lean recomputes
every successor and checks every claimed inequality; the exporters are outside
the trusted proof base. The exporters share deterministic tree and proof-piece
rendering in [`scripts/lean_export.py`](scripts/lean_export.py). All failures,
including exhausted row-search fuel, reject the calculation. A search branch is
never silently discarded to make the certificate pass.

## Reproducing the certificates

The generated Lean data are included in the repository; regeneration is not
required to build it. To regenerate all certificates and witnesses, run:

```sh
python3 scripts/export_finite_certificate.py
python3 scripts/export_kernel_checks.py
python3 scripts/export_forty_certificate.py
python3 scripts/export_run_witnesses.py
python3 scripts/export_run_lengths.py
python3 scripts/export_window_bounds.py
python3 scripts/build_kernel.py
lake build --wfail
lake lint -- --no-build
python3 scripts/check_axioms.py
```

The original Python verification programs can also be run independently:

```sh
python3 ../verification/verify_tuples.py
python3 ../verification/compare_verifiers.py
python3 ../verification/knuth_ranges.py
```

See the [companion-code guide](../README.md) for
its reference calculations and examples. Those programs supply candidate data;
the Lean checks establish the formal results.
