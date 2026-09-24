# Fast generator of the greedy queens

This directory contains the C11 generator of Section 7 of the paper. It
produces the exact greedy-queen rows q<sub>0</sub>, q<sub>1</sub>,
q<sub>2</sub>, … in order, with linear total work and logarithmic working
storage (Section 7.4), using 34925 bytes of fixed data. It needs no
graph or data files at run time. On the EC2 machine of Section 7.5 it generated
and checksummed ten billion rows in 25.413 s with a peak resident memory of
1.76 MiB, against 49.040 s and 6243.51 MiB for a bit-packed version of
Knuth's `infty-queens`.

The directory also contains the table builder and its finite checks, the
Knuth comparator, the benchmark tools, the scanner used to check Knuth's
ranges through c = 10<sup>11</sup> (the remark on 1-indexed coordinates in
Section 3), and the records of both measurements.
[REPORT.md](REPORT.md) describes the measurements in full.

## How the code follows Section 7

**Records (Section 7.2).** The local calculation keeps only the bounded
record w, z, R, D, A, the upper-column bits u<sub>m−4</sub> … u<sub>m−1</sub>,
and the queue Q. `LocalRule.step` in `tools/build_tables.py` is this
calculation, one queen per call. It starts from the board before column 30,
computed directly from the greedy rule, with w = 0, z = −1, R = A = ∅,
D = {1}, four upper bits 1111 and Q = `00322301212`.

**Paused records and classes (Section 7.3).** The builder runs the
calculation until it needs one more input symbol and pauses. Pairing each
paused record with the last twelve symbols of its input, and following every
edge of the history graph `../verification/history.json`, it reaches 2489
pairs. Dropping the histories leaves 300 paused records and 476 one-symbol
transitions (`generated/paused_records.json`). Compatible records are
grouped into 82 classes; every defined transition is checked against the
classes.

**Four-symbol table lookup (Section 7.3).** All 3483 paths of four input
transitions are formed on the 300-record graph, and each is checked against
the entry selected by its starting class and its four input symbols, packed
into one byte. The 1637 entries are packed into an array of 3262 64-bit
words, `qf_table` in `generated/tables.h`. Each class has a base offset in
this array, and the entry for input byte a is at base + a. An entry holds,
from the low bits up: the successor's base offset (12 bits), the number of
output symbols, 3 to 12 (4 bits), the output symbols, two bits each
(24 bits), and the offset of the entry's coordinate data in `qf_packets`
(14 bits).

**Coordinate decoding (Section 7.3).** The coordinate data of an entry
are its number of queens, the total advances of m and U across the block,
and one byte per queen. A lower queen's byte is its row offset from the row
reference m<sub>0</sub> at the start of the block. An upper queen's byte is
128 plus its offset from n<sub>0</sub> + U<sub>0</sub>. `decode` in
`src/queens_fast.c` adds the offset to the selected base. The first thirty
rows are stored as a seed, and the eighteen symbols
σ<sub>30</sub> … σ<sub>47</sub>, which need no input, are a first block.

**Chain of copies with halving buffers (Sections 7.1 and 7.4).** A `Copy`
in `src/queens_fast.c` is one inner copy of the calculation (Section 7.1). It
holds its table position, a buffer of ready bytes (four symbols each), and up
to three symbols not yet forming a byte. `refill` is the refill rule of Section 7.4: when the
buffer is empty it reads bytes from the next copy, which it creates on first
use, and applies one table lookup per byte until the buffer holds its budget.
The first inner copy has a budget of 1024 bytes and each further one half of
the previous one, down to one byte. Each buffer has three padding bytes. The
outer copy, `QFGenerator`, reads bytes from the first inner copy and decodes
rows. At 10<sup>10</sup> queens the chain has 42 levels and 3560 bytes of
heap.

**Separate check of the calculation.** `tests/local_rule_reference.c` is a
second implementation of the same local calculation, one queen per call,
with no table. The finite cases written by the builder are replayed through
it: all 874 local steps (574 complete steps and 300 requests for input) and
all 3483 four-input paths, comprising 24811 local steps.

## Directory map

| Path | Contents |
|---|---|
| `src/queens_fast.h` | The public interface |
| `src/queens_fast.c` | The generator: table lookups, chain of copies, coordinate decoding |
| `src/main.c` | The command-line program `queens_fast` |
| `src/scan_bounds.c`, `src/bounds_exact.h` | The scanner of Knuth's ranges, with exact integer comparisons |
| `tools/build_tables.py` | Builds everything in `generated/` from the history graph |
| `generated/tables.h` | The table, coordinate data and seed rows, included by the generator |
| `generated/local_cases.txt`, `generated/block_cases.txt` | The finite cases replayed by the C checks |
| `generated/paused_records.json` | The 300 paused records, their transitions and their 82 classes |
| `generated/construction_counts.json` | The counts checked during construction |
| `tests/local_rule_reference.c` | The separate implementation of the local calculation |
| `tests/check_local_steps.c`, `tests/check_table_paths.c` | Replay the finite cases and check the compiled table |
| `tests/check_coordinates.py` | Compares every coordinate of five programs with a full-occupancy calculation |
| `tests/test_api.c` | Tests the interface, including pauses inside a block |
| `tests/check_bounds.py` | Tests the scanner of Knuth's ranges |
| `tests/check_ec2_results.py` | Checks a benchmark campaign and recomputes the timing table |
| `tests/check_bounds_results.py` | Checks the recorded scan of Knuth's ranges |
| `knuth/knuth_packed.c` | The bit-packed Knuth comparator of Section 7.5 |
| `knuth/derive_knuth_packed.py` | Derives `knuth_packed.c` from Knuth's `infty-queens.w` |
| `bench/benchmark_native.c` | Launcher measuring elapsed time and peak memory of one process (Linux) |
| `bench/run_benchmark.py` | Runs a benchmark campaign like that of Section 7.5 |
| `bench/run_bounds_scan.py` | Runs and records a scan of Knuth's ranges |
| `results/` | The records of the two measurements, described below |
| `Makefile` | Builds the programs and runs the checks |
| `REPORT.md` | The measurement report |

## Quick start

A C11 compiler with `<stdint.h>` exact-width types and 8-bit bytes is enough
for the generator; the commands below also use `make` and a POSIX shell.
Python 3.10 or later (standard library only) is needed for the builder and
the tests, not for the generator.

```sh
make                                    # build/queens_fast and build/knuth_packed
./build/queens_fast --count 1000000
```

prints a one-line JSON summary:

```json
{"algorithm":"queens-fast-sparse-b4","count":1000000,"last_column":999999,"last_queen":1618033,"hash":"a1eacbe1584dcd3c","levels":23,"generator_bytes":48,"producer_record_bytes":32,"symbol_buffer_bytes":2124,"heap_bytes":2876,"static_data_bytes":34925,"algorithm_bytes":37801,"outer_macro_steps":0,"inner_macro_steps":0,"refill_calls":0,"seconds":0.002637000}
```

The count includes column 0, so the last column is N − 1, and `last_queen`
is q<sub>N−1</sub>. `hash` is a checksum of all N rows: starting from
14695981039346656037, each row y replaces h by (h XOR y) × 1099511628211
modulo 2<sup>64</sup>. `knuth_packed` computes the same checksum. The storage
fields come from `qf_stats`; `seconds` is processor time.

Add `--emit` to print every row as `column row`; the summary then goes to
standard error:

```sh
./build/queens_fast --count 10 --emit 2>/dev/null
```

```text
0 0
1 2
2 4
3 1
4 3
5 8
6 10
7 12
8 14
9 5
```

Without `make`:

```sh
cc -O3 -std=c11 -DNDEBUG -fwrapv src/queens_fast.c src/main.c -o queens_fast
```

### Using the C interface

Include `src/queens_fast.h` and compile `src/queens_fast.c` with your
program. Each generator resumes where the previous call stopped, and the
three output functions can be mixed freely, even inside a table block:

```c
#include "queens_fast.h"
#include <inttypes.h>
#include <stdio.h>

int main(void)
{
    QFGenerator *g = qf_create();
    uint64_t row, rows[1000];
    uint64_t hash = UINT64_C(14695981039346656037), last = 0;
    if (!g) return 1;
    if (qf_next(g, &row)                         /* q_0 */
        || qf_fill(g, rows, 1000)                /* q_1 ... q_1000 */
        || qf_hash(g, UINT64_C(1000000), &hash, &last)) {  /* q_1001 ... q_1001000 */
        perror("queens_fast");
        qf_destroy(g);
        return 1;
    }
    printf("next column %" PRIu64 ", last row %" PRIu64 "\n", qf_position(g), last);
    qf_destroy(g);
    return 0;
}
```

The functions return 0 on success and −1 with `errno` set on failure; after
an allocation failure, destroy the generator. Columns are limited to
[0, 2<sup>63</sup> − 1). See `src/queens_fast.h` for details.

Two compile-time options exist for experiments: `-DQF_BUFFER=B` sets the
initial buffer budget (default 1024; `make test` also runs a build with
B = 1), and `-DQF_INSTRUMENT` makes the summary report the number of table
lookups and buffer refills.

## Checking the generator

```sh
make verify     # about a second
make test       # about ten seconds
make sanitize
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 UBSAN_OPTIONS=halt_on_error=1 \
  ./build/test_api_sanitize
```

`make verify` rebuilds every file of `generated/` in memory from
`../verification/history.json` and checks that it is identical to the
files present, then replays the finite cases through the separate
implementation:

```text
{"verified":true,"cases":874,"completed_steps":574,"input_requests":300}
{"verified":true,"four_input_paths":3483,"local_steps":24811}
```

The builder asserts every construction count, including the 300 paused
records, the 82 classes, the bound z − |Q| ≥ −4 at every paused record used
in the lead inequality of Section 7.4, and the first pause at n = 48, m = 29, κ = 17. The history graph
is read only here; its own verification is in `../verification/`.

`make test` compares every coordinate of the first million queens, for the
release build, an assertion-enabled build, a build with every buffer budget
equal to one, the separate implementation, and `knuth_packed`, with a
calculation using full occupancy arrays, whose first 3000 rows are checked
against the literal greedy rule. It also checks the command line on all
counts up to 256 and at buffer boundaries, and runs `build/test_api`.
`make sanitize` builds the command-line program and the interface test with
AddressSanitizer and UndefinedBehaviorSanitizer.

After changing the builder, run `make regen` to rewrite `generated/`, then
repeat all the checks.

These are finite tests. Correctness of every row is proved in Section 7.4; the
tests check that the program implements the construction it describes.

## Reproducing the timing table

The benchmark needs Linux (`fork`, `wait4` and CPU affinity). Build with the
default flags and run the campaign, choosing an idle logical CPU:

```sh
make all build/benchmark_native
python3 bench/run_benchmark.py --cpu 2 --output results/new-benchmark.json \
  --counts 1000000 10000000 100000000 1000000000 10000000000
python3 tests/check_ec2_results.py results/new-benchmark.json
```

For each count, each program runs once as an excluded warmup and three times
more, in alternating order, as fresh processes pinned to the chosen CPU. The
second script checks the runs and prints medians and ranges of elapsed time
and peak memory, the ratios of the medians, and the last row and checksum at
each count. The largest count needs about 6.1 GiB of memory for
`knuth_packed` and takes about six minutes on the EC2 machine.

To recheck the recorded EC2 campaign itself:

```sh
python3 tests/check_ec2_results.py --environment results/ec2-environment.json
```

## Reproducing the check of Knuth's ranges

The scanner needs GCC or Clang, for their 128-bit integers; do not add
`-ffast-math`.

```sh
make build/scan_bounds build/knuth_packed
python3 tests/check_bounds.py                    # a few seconds
python3 bench/run_bounds_scan.py --count 100000000000 --prefix results/new-knuth-bounds
python3 tests/check_bounds_results.py            # checks the recorded scan
```

For every column c ≤ 10<sup>11</sup> the scanner checks that s(c) = q<sub>c−1</sub> + 1
lies in [c/φ − 3, c/φ + 5] ∪ [cφ − 2, cφ + 1], and also checks each interval
on its own side of the diagonal. It records the extreme deviations with the
queens attaining them. Comparisons that floating-point arithmetic cannot
decide with a proved error bound are made exactly, with 128-bit integers.
The recorded scan took 11 minutes on a desktop machine; its results are in
REPORT.md.

## The Knuth comparator

`knuth/knuth_packed.c` is derived from Donald Knuth's CWEB program
[`infty-queens`](https://www-cs-faculty.stanford.edu/~knuth/programs/infty-queens.w).
Its array allocation and queen-placement code are Knuth's, taken verbatim
from the output of CTANGLE, with two changes: the occupancy flags are stored
as bits in 64-bit words, and counts and indices are 64-bit integers. The
placement order and control flow are Knuth's. The surrounding program, which
reads `--count N [--emit]`, prints zero-based rows and computes the checksum,
is ours. The repository's MIT License covers our code; the code taken from
`infty-queens` remains Knuth's. `knuth/derive_knuth_packed.py` performs the
derivation; with the
`ctangle` program installed, run

```sh
python3 knuth/derive_knuth_packed.py --check
```

to download `infty-queens.w` and confirm that it yields `knuth_packed.c`
exactly (or pass `--source` with a local copy).

## Recorded results

| File | Contents |
|---|---|
| `results/ec2-native.json` | Every run of the campaign behind the timing table: 10 warmups and 30 timed runs, each with the launcher's statistics and the program's summary |
| `results/ec2-native.csv` | Medians, minima and maxima of elapsed and processor time |
| `results/ec2-environment.json` | The EC2 instance, operating system, compiler, CPU topology and build flags, recorded separately on the machine |
| `results/ec2-validation.json` | The output of `tests/check_ec2_results.py` for the campaign: the timing table's medians and ranges, the storage at each count, and the signatures |
| `results/knuth-bounds-1e11.json` | The final record of the scan through c = 10<sup>11</sup> |
| `results/knuth-bounds-1e11-progress.log` | A record every 10<sup>9</sup> columns |
| `results/knuth-bounds-1e11-environment.json` | The machine, compiler, command and elapsed time of the scan |
