# Kernel-only finite verification

The project's computational proofs use ordinary Lean proof terms. In
particular, `decide +kernel` asks the Lean kernel to check a proposition by
reducing its decidable instance. It does not introduce a native-evaluation
axiom. The acceptance criterion for every imported project declaration is that
Lean's axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Data and proofs

The Python programs generate candidate data: history graphs, state tables,
indexed successor lists, finite greedy prefixes, permitted path lengths, and
window bounds.
These programs are outside the trusted proof base. A wrong entry either makes
a Lean check fail or must still satisfy the precise mathematical property
established by the checker.

The finite checks have two separate parts:

1. A general Lean theorem proves what a successful checker establishes.
2. Kernel reduction proves that the supplied finite input passes that checker.

For example, the bitboard checker proves that each proposed row is unattacked
and every smaller row is attacked. Its soundness theorem then identifies the
entire checked prefix with `Queens.q`, which is defined independently by the
least-unattacked-row rule. Occurrences needed for Corollary 20 therefore concern
the actual greedy sequence.

## Efficient evaluation without additional trust

Kernel evaluation benefits from different data layouts than compiled execution.
The generated binary trees permit lookup along a short branch. Their lookup
soundness theorems establish that a returned value is an actual tree entry;
balance is a performance consideration, not an assumption in that proof.
Separate alignment checks connect these trees to the mathematical tables.

History well-formedness uses a proved tree checker for strict key bounds and
closure under every permitted symbol. This establishes the original
well-formedness predicate, including uniqueness, instead of weakening it to
accommodate the representation.

Large checks are divided into bounded pieces and assembled using general
soundness lemmas. Each piece has its own kernel-checked proof. This limits
reduction caches and permits independent compilation. The local calculation
still explores every permitted branch; any failed request or exhausted search
rejects the certificate.

The largest transition check has four independently compiled parts. A cold
build takes substantial computation; Lake caches each completed part. To
control peak memory, `python3 scripts/build_kernel.py` builds the large checks
in stages and these four parts sequentially. Add `--parallel-forty` to compile
the four parts together. Both commands run the same kernel proofs and finish
with the ordinary full build. Staging limits simultaneous work; it does not
make every individual check small.

Measured on a 10-core Apple-silicon machine with 24 GiB of memory, from a cold
build (mathlib downloaded, project outputs removed). Memory is the peak total
resident size of all Lean processes during the stage.

| Stage (`build_kernel.py`) | Time | Peak memory |
|---|---:|---:|
| `Certificate` (Proposition 18) | 141 s | 7.3 GiB |
| `WindowCertificate` (Proposition 24) | 62 s | 8.0 GiB |
| `StateCounts` | 72 s | 1.8 GiB |
| `Reachability` | 154 s | 3.4 GiB |
| `FortyHistoryChecks` | 72 s | 6.4 GiB |
| `FortySeed` | 19 s | 4.2 GiB |
| `FortyStateChecksPart0`–`3`, one at a time | 370 + 359 + 359 + 359 s | 4.9 GiB |
| the same four parts with `--parallel-forty` | 429 s | 10.2 GiB |
| `FortyCertificate` | 21 s | 7.4 GiB |
| `RunWitnesses` | 9 s | 3.2 GiB |
| `RepeatedRunCertificate` | 192 s | 8.9 GiB |
| remaining modules (`lake build`) | 23 s | 13.2 GiB |

The total is about 37 minutes with the default staging and about 20 minutes with
`--parallel-forty`. The last stage compiles many small modules at once; its peak
is the sum over up to ten concurrent Lean workers and scales with the number of
cores, while the largest single process is the repeated-run check.

The forty-symbol verification uses the same parameterized local calculation
and semantic correctness theorem as the twelve-symbol verification. An indexed
infinite path is proved to represent the actual greedy board before its edges
are contracted into lower-run lengths.

For repeated lower-run lengths, the graph certificate checks finite sets of
possible remaining lengths and their closure under prepending an edge. The
boundary checks restrict maximal repetitions to `{1, …, 9, 11}`. Separate
nonemptiness and upper-bound checks exclude twelve consecutive equal terms,
so the argument also rules out an infinite constant tail. Checked prefix
witnesses supply every claimed value and handle runs crossing the starting
boundary of the refined graph.

## Window bounds in `ℚ(√5)`

Proposition 24 needs the window bounds `lo` and `hi` exactly: some of its
inequalities hold with equality, and the strictness of Theorem 2 uses the exact
constants. Every value lies in `ℚ(√5)` with denominator dividing 8, so the
certificate stores `8 lo(W)` and `8 hi(W)` as elements of mathlib's `ℤ√5`.
Multiplying each inequality by 16 clears all denominators, since
`16 / φ = 8 (√5 - 1)` and `16 / φ² = 24 - 8√5`. Mathlib's order on `ℤ√5` is
decided by comparing squares of integers, and `Queens.sqrtFiveEval_le` proves
that the evaluation map into `ℝ` is monotone. A kernel-checked comparison in
`ℤ√5` is therefore a real inequality, with no rounding.

The checks run on the same state table as Proposition 18. For each state, the
check looks up the window bounds of both histories, verifies the two inequalities
of Definition 22, recomputes `calculateChoices` (every branch of the candidate
phase of Algorithm 1), and verifies property (ii) and `w - r - |D| ≤ 2` at every
lower choice. A failed lookup or calculation rejects the state. A second check
visits every entry of the window-bound tree and of the history-graph tree, so
the bounds are defined at every vertex, property (i) holds where required, and
every vertex is the output history of a listed state. The exporter computes the
bounds with the reference program `verification/knuth_ranges.py`; Lean does not
depend on how they were found.

## Repeating the audit

From the project root:

```sh
lake build
lake lint -- --no-build
python3 scripts/check_axioms.py
python3 scripts/declaration_index.py
```

`AxiomAudit.lean` prints the principal declarations' dependencies and also
inspects every imported project declaration, including private helpers and
generated certificate pieces. Lean computes their actual proof dependencies.
The audit script rejects additional axioms and saves the successful output to
`docs/AXIOMS.txt`. The declaration index records the public API and its
paper-correspondence comments.

The Lake configuration enables mathlib's standard source linters during builds;
the lint command also checks the imported project's declarations. Generated
certificate files document their line/file length exceptions, and large evaluation
budgets are local to the checked declarations. The downstream project does not
require mathlib's copyright-header format.

The certificate generators are kept in `scripts/`. They read the reference
programs in `verification/` and `oeis/`, which are not part of the trusted base.
