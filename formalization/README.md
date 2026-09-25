# Greedy Queens and the Golden Ratio

This directory formalizes Boon Suan Ho's *Greedy Queens and the Golden Ratio*
in Lean 4 with mathlib. It is a self-contained Lake project within the
[companion-code repository](../README.md).

**Paper:** [Greedy Queens and the Golden Ratio (PDF)](https://boonsuan.github.io/queens.pdf).

The formalization proves Theorem 1 and its supporting results, Corollaries 18–19,
Lemma 20, and Proposition 21 for the sequence defined by the greedy placement rule.
All proofs, including the finite computation, are checked by the Lean kernel.
There are no `sorry`s, custom axioms, or native-evaluation axioms.

## Where to start

- **Read the result:** the [main theorem](#the-main-theorem) below states the two
  golden-ratio bounds directly in Lean.
- **Follow the proof:** the [paper-to-code table](#paper-to-code-correspondence)
  gives a route through the modules; the [declaration index](docs/DECLARATIONS.md)
  records the purpose and paper correspondence of individual definitions and results.
- **Check the formalization:** follow [Build and check](#build-and-check).
  [`Queens.lean`](Queens.lean) imports the complete formalized result set.
- **Inspect the finite verification:** read the [verification design](docs/KERNEL_VERIFICATION.md)
  and the [axiom audit](docs/AXIOMS.txt). The original manuscript and reference
  programs are preserved in [`queens-formalization-kit/`](queens-formalization-kit/README.md).

## The main theorem

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
numbers, and `Real.goldenRatio` is mathlib's golden ratio. The origin has `q 0 = 0`;
every other queen lies strictly above or below the main diagonal.

[`bounded_diagonal_discrepancy`](Queens/Exactness.lean) is the proved Lemma 5.
[`main_of_diagonalDiscrepancy`](Queens/Main.lean) separates the mathematical
deduction from that lemma from the finite computation used to establish it.
The final theorem above has no unproved discrepancy or finite-state hypothesis.

## The greedy definition

[`Queens/Greedy.lean`](Queens/Greedy.lean) starts with the placement rule itself.
These excerpts are also inside `namespace Queens`:

```lean
def Available (n r : ℕ) (previous : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, r ≠ previous i ∧ r + i.val ≠ previous i + n ∧
    r + n ≠ previous i + i.val
```

`Fin n` indexes the earlier columns `0, …, n − 1`. The three inequalities exclude
attacks along rows, diagonals, and antidiagonals. The lemma `exists_available`
proves that an available row always exists, so the sequence is defined by:

```lean
noncomputable def q (n : ℕ) : ℕ :=
  Nat.find (exists_available n (fun i => q i.val))
termination_by n
```

`Nat.find` chooses the least row satisfying the predicate; recursion only refers
to earlier columns. The theorems `q_available` and `q_le_of_available` express
availability and minimality. [`q_bijective`](Queens/Permutation.lean) proves
Lemma 3: every nonnegative row is eventually used exactly once.

The mathematical definition is marked `noncomputable`. Numerical witnesses are
handled by a separate, proved [finite-prefix checker](Queens/Finite/GreedyPrefix.lean),
which identifies every accepted row with this same `q`.

## Formalized scope

Besides Theorem 1 and the lemmas establishing it, the project includes:

- **Corollary 18:** [`q_diagonal_bijective`](Queens/DiagonalCoverage.lean) proves
  that every signed diagonal contains exactly one queen.
- **Corollary 19:** all five range assertions, including both exclusion of other
  values and occurrence of every listed value in the actual greedy sequence.
- **Lemma 20:** [`exact_error_recursion`](Queens/ErrorRecursion.lean), the exact
  counting-error identity.
- **Proposition 21:** [`sharper_bounds`](Queens/SharperBounds.lean), the sharper
  asymmetric bounds for both upper and lower queens.

Corollary 19 gives the following exact ranges:

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

**Outside the formalized scope:** Section 7's fast-generation algorithm and
Proposition 22, and the unnumbered return-word catalogues following Corollary 19.
Result numbers refer to the [preserved manuscript](queens-formalization-kit/paper/queens.pdf).

## Paper-to-code correspondence

The proof has three parts. First, the mathematical argument in Sections 2–3
deduces the golden-ratio estimates from bounded diagonal discrepancy. Next,
Sections 4–5 prove that finite local records retain the actual greedy step.
Finally, Section 6 checks a closed finite invariant and follows the actual board
indefinitely to establish the discrepancy bound. Module introductions and
declaration docstrings explain the correspondence in more detail.

| Paper | Lean module | Main declarations |
|---|---|---|
| Introduction; Lemma 2 | [`Greedy`](Queens/Greedy.lean) | `q`, `q_available`, `q_le_of_available`, `q_eq_add_upperCount` |
| Lemma 3 | [`Permutation`](Queens/Permutation.lean) | `no_antidiagonal_tail`, `q_surjective`, `q_bijective` |
| Lemma 4 | [`LowerRows`](Queens/LowerRows.lean) | `sortedLowerRow`, `sortedLowerRow_eq` |
| Lower columns and ranks, §§2–3 | [`LowerColumns`](Queens/LowerColumns.lean) | `lowerColumn`, `lowerCount_lowerColumn`, endpoint inequalities |
| Lemma 6 | [`Sorting`](Queens/Sorting.lean), [`Main`](Queens/Main.lean) | `abs_sub_le_of_monotone_rearrangement`, `lower_column_discrepancy` |
| Lemma 7 | [`Counting`](Queens/Counting.lean) | `counting_recurrence_int`, `counting_recurrence` |
| Proposition 8; Theorem 1 from Lemma 5 | [`GoldenRatio`](Queens/GoldenRatio.lean), [`Main`](Queens/Main.lean) | `count_error_lt`, `position_bounds_of_diagonalDiscrepancy`, `main_of_diagonalDiscrepancy` |
| Definition 9 | [`Word`](Queens/Word.lean) | `columnBit`, `upperRowBit`, `queenSymbol` |
| Definition 10; equation (local-rank) | [`LocalBoard`](Queens/LocalBoard.lean) | `rowReference`, `diagonalReference`, `local_rank_identity` |
| Propositions 12–13 | [`LocalGeometry`](Queens/LocalGeometry.lean), [`RowCounts`](Queens/RowCounts.lean), [`LocalSources`](Queens/LocalSources.lean) | relative source geometry, row-count adjustment, exact executable tests |
| Operational candidate selection, Lemma 16 | [`LocalChoice`](Queens/LocalChoice.lean) | `chooseFrom_contains_actual` |
| Branching and final update, Lemma 16 | [`Finite/Branching`](Queens/Finite/Branching.lean), [`Finite/FinishSemantics`](Queens/Finite/FinishSemantics.lean) | `allBranches_branch`, `finishChoice_contains_actual` |
| Candidate selection, §4 | [`LocalCandidates`](Queens/LocalCandidates.lean) | `available_candidate_iff`, `q_eq_candidate_iff` |
| Actual-state interpretation | [`LocalRepresentation`](Queens/LocalRepresentation.lean) | `RecordsRepresented`, `StateRepresented` |
| Reference searches and record updates, §§4–5 | [`LocalAdvances`](Queens/LocalAdvances.lean), [`LocalUpdates`](Queens/LocalUpdates.lean) | row advance bound, exact set/reference updates |
| Requests and causality, Lemma 16(i) | [`LocalRequests`](Queens/LocalRequests.lean), [`LocalBounds`](Queens/LocalBounds.lean) | actual permitted paths and queue extension |
| Algorithm 1 | [`Finite/Local`](Queens/Finite/Local.lean) | total branching `calculate` |
| Definition 11; history encoding | [`Finite/Encoding`](Queens/Finite/Encoding.lean), [`Finite/HistoryCore`](Queens/Finite/HistoryCore.lean), [`Finite/History`](Queens/Finite/History.lean) | encoding round trips, general history paths, graph well-formedness and counts |
| Proposition 17 | [`Finite/Certificate`](Queens/Finite/Certificate.lean) | `certificate_checked`, `certified_successors`, `reachable_condition` |
| Starting checks, §6.1 | [`Finite/PrefixTransfer`](Queens/Finite/PrefixTransfer.lean), [`Finite/Seed`](Queens/Finite/Seed.lean) | shared prefix-to-board identities, `q_eq_seedRow`, `initialState_represented`, initial word path |
| Infinite induction, §6.4 | [`Identification`](Queens/Identification.lean) | `actualInvariant_of_localStepExact`, `diagonalDiscrepancy_of_localStepExact` |
| Lemma 16, Lemma 5, Theorem 1 | [`Exactness`](Queens/Exactness.lean) | `local_step_exact`, `bounded_diagonal_discrepancy`, `main` |
| Corollary 18 | [`DiagonalCoverage`](Queens/DiagonalCoverage.lean) | `q_diagonal_bijective`, `existsUnique_queen_on_diagonal`, `lowerDiagonal_bijOn` |
| Corollary 19, runs and gaps | [`RunsAndGaps`](Queens/RunsAndGaps.lean) | `lower_column_run_lengths`, `upper_column_run_lengths`, `upper_column_gaps`, `lower_column_gaps` |
| Corollary 19, lower-run sequence | [`LowerRuns`](Queens/LowerRuns.lean), [`LowerRunCoverage`](Queens/LowerRunCoverage.lean) | `lowerRunLength`, `existsUnique_lowerRun_of_maximal`, `lowerRunLength_range` |
| Corollary 19, repeated run lengths | [`LabeledRuns`](Queens/LabeledRuns.lean), [`RepeatedRuns`](Queens/RepeatedRuns.lean) | `RunLengthCertificate`, `repeated_lower_run_lengths`, `no_ten_repeated_lower_runs` |
| Corollary 19, finiteness of repetitions | [`RunsCoverage`](Queens/RunsCoverage.lean), [`RepeatedRunCoverage`](Queens/RepeatedRunCoverage.lean) | `no_twelve_equal_lower_run_lengths`, `existsUnique_repeated_lower_run_contains` |
| Corollary 19, occurrence witnesses | [`Finite/GreedyPrefix`](Queens/Finite/GreedyPrefix.lean), [`Finite/RunWitnesses`](Queens/Finite/RunWitnesses.lean), [`Finite/LowerRunWitnesses`](Queens/Finite/LowerRunWitnesses.lean) | proved greedy-prefix checker; actual run and gap witnesses |
| Lemma 16 with general history length | [`GeneralExactness`](Queens/GeneralExactness.lean) | `local_choices_exact_of_memory`, `local_step_exact_of_memory` |
| Corollary 19, forty-symbol refinement | [`Finite/FortyCertificate`](Queens/Finite/FortyCertificate.lean), [`Finite/FortySeed`](Queens/Finite/FortySeed.lean), [`FortyPath`](Queens/FortyPath.lean) | checked closed invariant, represented initial state, `actualVertex_represents`, `actualVertex_step` |
| Appendix A, run-graph contraction | [`Finite/PathContraction`](Queens/Finite/PathContraction.lean), [`Finite/RepeatedRunCertificate`](Queens/Finite/RepeatedRunCertificate.lean) | `runTargets_mem`, `repeatedRunCertificate` |
| Lemma 20 | [`ErrorRecursion`](Queens/ErrorRecursion.lean) | `referenceLowerRank_lt`, `exact_error_recursion` |
| Proposition 21, finite bounds | [`Finite/SharpBounds`](Queens/Finite/SharpBounds.lean), [`SharpRecords`](Queens/SharpRecords.lean) | `sharp_certificate_checked`, `sharp_record_bounds`, `lower_diagonal_discrepancy_le_two` |
| Proposition 21, analytic conclusion | [`GoldenRatio`](Queens/GoldenRatio.lean), [`SharpAnalysis`](Queens/SharpAnalysis.lean), [`SharperBounds`](Queens/SharperBounds.lean) | `sharp_error_bounds_of_recursion`, `sharp_count_error`, `sharper_bounds` |
| Exact reached-state set, Proposition 17 | [`Finite/Reachability`](Queens/Finite/Reachability.lean) | `certified_iff_reachable`, `reached_state_count`, `reached_edge_count` |

The paper indexes lower queens and sorted lower rows starting at one. Lean uses
zero-based indices: `lowerColumn k`, `lowerDiagonal k`, and `sortedLowerRow k`
correspond to the paper's rank `k + 1`. Board columns and rows are zero-based in both.
Signed differences are taken in `ℤ` or `ℝ`, avoiding truncated natural subtraction.
The golden ratio is mathlib's `Real.goldenRatio = (1 + √5) / 2`.

## Build and check

The project pins Lean `v4.33.1` and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`; transitive dependencies are pinned in
`lake-manifest.json`.

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
parts together. A cold build can take tens of minutes and substantial memory:
those four workers together use roughly 10 GiB, and one repeated-run check has
used about 9 GiB on its own. See the
[build details](docs/KERNEL_VERIFICATION.md). Completed proofs are cached by Lake.
After the first build, `lake build --wfail` is sufficient for incremental checks.

The reference kit in this directory is the preserved snapshot used to generate
the certificates. Keeping that snapshot makes regeneration independent of later
changes to the Python and C programs elsewhere in the repository.

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

The [Lean workflow](../.github/workflows/formalization.yml) runs on pull requests
to `main` and pushes to `main` that change `formalization/**` or the workflow
itself. Changes confined to the other companion programs do not trigger it.
It can also be run manually from GitHub's Actions tab.

CI builds the proofs with warnings treated as errors, runs the declaration
linters and kernel-only axiom audit, checks the declaration documentation, and
regenerates the certificates to verify that they match the committed files.
It uses the pinned toolchain and dependencies, stages the large kernel checks,
and caches successful builds for incremental checking.

## Finite verification and trust

The history graph has **2,092 vertices and 2,603 labeled edges**. The candidate invariant
contains **7,014 distinct states**, whose recomputed successor sets have **8,327 directed
edges**. Each state satisfies Condition 15, every calculation succeeds, and every
successor belongs to the same invariant. These statements are checked by Lean.
A separate checked predecessor certificate proves that every listed state is reachable,
so the table is exactly the reached-state set, not merely a closed superset.

Computational proofs use `decide +kernel` and ordinary checker-soundness
lemmas. Balanced lookup trees and bounded certificate pieces make these checks
practical without adding compiler-evaluation axioms. `AxiomAudit.lean` prints
the dependencies of the principal results and inspects every imported project
declaration, including private helpers. `scripts/check_axioms.py` rejects
anything beyond `propext`, `Classical.choice`, and `Quot.sound`.

Proposition 21 checks stronger record and candidate-choice inequalities on the
same 7,014 states. Its analytic argument and exact error recursion are separate
from the finite checker. Corollary 19 additionally uses a forty-symbol history
graph, an indexed actual-state path, proved path contractions, and independently
verified greedy-prefix witnesses for attainment.

The forty-symbol invariant has 29,267 indexed entries and 30,000 indexed edges;
its history graph has 16,876 entries and 17,499 labeled edges. For this refinement
the proof establishes a closed invariant containing the actual path. It does
not require a separate exact-reachability or distinct-state count theorem.

The Python exporters supply only candidate data and witnesses. Lean recomputes
every successor; the exporters are outside the trusted proof base.
The exporters share deterministic tree and proof-piece rendering in
[`scripts/lean_export.py`](scripts/lean_export.py).
All failures, including exhausted row-search fuel, reject the calculation. A search
branch is never silently discarded to make the certificate pass.

## Reproducing the certificates

The generated Lean data are included in the repository; regeneration is not
required to build it. To regenerate all certificates and witnesses, run:

```sh
python3 scripts/export_finite_certificate.py
python3 scripts/export_kernel_checks.py
python3 scripts/export_forty_certificate.py
python3 scripts/export_run_witnesses.py
python3 scripts/export_run_lengths.py
python3 scripts/build_kernel.py
lake build --wfail
lake lint -- --no-build
python3 scripts/check_axioms.py
```

The original Python verification programs can also be run independently:

```sh
python3 queens-formalization-kit/companion/verification/verify_tuples.py
python3 queens-formalization-kit/companion/verification/compare_verifiers.py
```

See the [companion-code guide](queens-formalization-kit/companion/README.md) for
its reference calculations and examples. Those programs supply candidate data;
the Lean checks establish the formal results.
