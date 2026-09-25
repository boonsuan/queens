# Kernel-only finite verification

The project's computational proofs use ordinary Lean proof terms. In
particular, `decide +kernel` asks the Lean kernel to check a proposition by
reducing its decidable instance. It does not introduce a native-evaluation
axiom. The acceptance criterion for every imported project declaration is that
Lean's axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Data and proofs

The Python programs generate candidate data: history graphs, state tables,
indexed successor lists, finite greedy prefixes, and permitted path lengths.
These programs are outside the trusted proof base. A wrong entry either makes
a Lean check fail or must still satisfy the precise mathematical property
established by the checker.

The finite checks have two separate parts:

1. A general Lean theorem proves what a successful checker establishes.
2. Kernel reduction proves that the supplied finite input passes that checker.

For example, the bitboard checker proves that each proposed row is unattacked
and every smaller row is attacked. Its soundness theorem then identifies the
entire checked prefix with `Queens.q`, which is defined independently by the
least-unattacked-row rule. Occurrences needed for Corollary 19 therefore concern
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
the four parts together, using roughly 10 GiB for their Lean workers. Both
commands run the same kernel proofs and finish with the ordinary full build.
Staging limits simultaneous work; it does not make every individual check small.
The repeated-run certificate's alignment check has used about 9 GiB on its own.

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

The original manuscript and reference programs remain byte-for-byte unchanged
from the supplied archive. Certificate generators are kept in `scripts/`.
