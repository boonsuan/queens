# Measurement report

This report describes the two computations with the fast generator that the
paper reports: the timing and memory comparison of Section 7.5,
and the check of Knuth's ranges through c = 10<sup>11</sup> (the remark on
1-indexed coordinates in Section 3). The README explains the code and how to
repeat both.

## 1. Generation and hashing (Section 7.5)

### What was measured

Two programs generated the first M rows q<sub>0</sub>, …, q<sub>M−1</sub>
(the count M includes the origin) and folded every row, in order, into the
same 64-bit checksum, then printed one summary line. Neither retained the
sequence.

- `queens_fast`: the table-driven generator of Section 7, through its bulk
  function `qf_hash`, with the default table and initial buffer budget 1024.
- `knuth_packed`: Knuth's `infty-queens` with its occupancy arrays packed one
  bit per flag into 64-bit words and 64-bit indices, keeping Knuth's
  placement order and control flow (see `knuth/`).

The measurement is bulk generation with a checksum. It does not measure
row-at-a-time calls or printed output.

### Results

Medians of three timed runs, with the smallest and largest of the three in
brackets. Elapsed time is from process creation to exit; memory is the
peak resident set size reported by the kernel (1 MiB = 2<sup>20</sup> bytes).

| M | Our C (s) | Packed Knuth (s) | Ratio | Our C (MiB) | Packed Knuth (MiB) |
|---:|---:|---:|---:|---:|---:|
| 10<sup>6</sup> | 0.003 [0.003, 0.003] | 0.005 [0.005, 0.005] | 1.76 | 1.76 | 2.20 |
| 10<sup>7</sup> | 0.026 [0.026, 0.027] | 0.049 [0.049, 0.049] | 1.89 | 1.67 | 7.82 |
| 10<sup>8</sup> | 0.253 [0.253, 0.253] | 0.486 [0.486, 0.487] | 1.92 | 1.76 | 64.07 |
| 10<sup>9</sup> | 2.524 [2.523, 2.525] | 4.862 [4.848, 4.864] | 1.93 | 1.67 | 625.88 |
| 10<sup>10</sup> | 25.413 [25.381, 25.414] | 49.040 [49.037, 49.155] | 1.93 | 1.76 | 6243.51 |

The ratio is the packed-Knuth median divided by ours. At ten billion queens
our generator took 25.413 s against 49.040 s, a speedup of 1.93, and its
peak resident memory was 1.76 MiB against 6243.51 MiB. From 10<sup>9</sup>
to 10<sup>10</sup> queens both times grew by a factor of about ten,
consistent with linear running time.

All eight runs at each count, warmups included, ended at the same last row
and checksum:

| M | q<sub>M−1</sub> | Checksum |
|---:|---:|---|
| 10<sup>6</sup> | 1618033 | `a1eacbe1584dcd3c` |
| 10<sup>7</sup> | 16180339 | `e90ab7b7e59e99ad` |
| 10<sup>8</sup> | 161803397 | `ea78393604ed1025` |
| 10<sup>9</sup> | 1618033987 | `264e17a4d3b5354d` |
| 10<sup>10</sup> | 16180339886 | `fa45508ddb884185` |

### Storage

The resident memory of our generator is almost entirely code, the C runtime
and the stack; the storage it requests itself is much smaller. Its fixed
data, compiled into the executable, are

| Fixed data | Bytes |
|---|---:|
| Table: 3262 entries of 8 bytes | 26096 |
| Coordinate data of 801 distinct output lists | 8799 |
| The thirty seed rows | 30 |
| Total | **34925** |

At 10<sup>10</sup> queens the chain has 42 levels, the outer copy and 41
inner copies, and the heap requested is

| Heap at 10<sup>10</sup> queens | Bytes |
|---|---:|
| The outer copy | 48 |
| 41 inner copies, 32 bytes each | 1312 |
| Their buffers: budgets 1024, 512, …, 1 and thirty more of 1, plus 3 padding bytes each | 2200 |
| Total | **3560** |

These numbers exclude allocator overhead and the stack. The number of levels
grows logarithmically: 23, 27, 32, 37 and 42 levels at M = 10<sup>6</sup>,
…, 10<sup>10</sup>, with 2876, 3020, 3200, 3380 and 3560 bytes of heap. At
these sizes this storage fits in memory pages that the process has already
allocated, so the measured resident memory does not grow.

Knuth's program allocates three occupancy arrays whose sizes grow with M. In
the packed version they take (2φ + 2)M/8 + O(1) ≈ 0.6545M bytes:
6545084984 bytes at M = 10<sup>10</sup>, which is 6241.88 MiB of the
6243.51 MiB measured.

### Linear projections

Neither program was run beyond 10<sup>10</sup> queens in this campaign. The
following extrapolates the 10<sup>10</sup> medians linearly; these are
projections, not measurements.

| M | Our C, projected | Packed Knuth, projected | Packed arrays |
|---:|---:|---:|---:|
| 10<sup>11</sup> | 4.24 min | 8.17 min | 65.5 GB (61.0 GiB) |
| 10<sup>12</sup> | 0.71 h | 1.36 h | 655 GB (610 GiB) |

Knuth's arrays at 10<sup>11</sup> queens already come close to the 64 GiB of
the EC2 machine, and at 10<sup>12</sup> need far more memory than it has, so
his projected times assume a machine with enough memory of comparable speed.
Paging or allocation failure would invalidate the extrapolation. Our
generator's fixed data stay the same and its heap grows by a few hundred
bytes; its 64-bit counters cover these counts. Keeping 10<sup>12</sup> rows
as 64-bit integers would itself take 8 TB, so small working storage matters
when the rows are used as they are produced.

### Machine and build

- Amazon EC2 `r7i.2xlarge`, region `ap-southeast-1`, freshly launched on
  23 September 2026: Intel Xeon Platinum 8488C, 8 vCPUs (4 cores with 2
  threads each), 64 GiB of memory (`MemTotal` 64774332 kB), no swap.
- Ubuntu 24.04.4 LTS, Linux 7.0.0-1012-aws, GCC 13.3.0
  (Ubuntu 13.3.0-6ubuntu2~24.04.1), Python 3.12.3.
- Both programs: `-O3 -std=c11 -DNDEBUG -fwrapv -Wall -Wextra -Wpedantic`,
  with no architecture-specific options. The launcher:
  `-O2 -std=c11 -Wall -Wextra -Wpedantic`.
- Every run was pinned to logical CPU 2, which shares its core with CPU 6.
  Nothing else ran during the campaign. The instance did not expose
  frequency or turbo controls.

### Procedure

1. On the instance, the programs were built with `make`, and the
   correctness checks were run first: the tables were rebuilt and compared,
   all 874 local cases and all 3483 four-input paths (24811 local steps)
   were replayed against the separate implementation, and every coordinate
   of the first million queens was compared with a full-occupancy
   calculation, for the release, assertion and sanitizer builds and for
   `knuth_packed`.
2. The machine description `results/ec2-environment.json` was recorded
   separately, before the campaign.
3. The campaign was run with `bench/run_benchmark.py` for M = 10<sup>6</sup>,
   10<sup>7</sup>, 10<sup>8</sup>, 10<sup>9</sup>, 10<sup>10</sup>. For each
   M, each program ran once as a warmup, which is not counted, and then three
   times, alternating which program ran first. All runs were sequential, in
   fresh processes.
4. Each run was started by the native launcher `bench/benchmark_native.c`. It
   reads `CLOCK_MONOTONIC` immediately before `fork` and after `wait4`
   returns, so the elapsed time includes program loading, initialization,
   generation, the checksum, the summary line, freeing memory and exit, but
   not the start of the launcher or of Python. Peak resident memory is the
   `ru_maxrss` that `wait4` reports; memory is never sampled during a run.
   Starting runs from a small native process, rather than from Python,
   keeps Python's memory out of the child's peak.
5. `tests/check_ec2_results.py` checked the runs and computed the medians
   (`results/ec2-validation.json`).

Each run also records the program's own processor time for initialization
and generation (`generation_cpu_seconds`), the elapsed time seen by the
Python driver (`driver_wall_seconds`), and the kernel's CPU times, page
faults and context switches. No run had a major page fault.

## 2. The check of Knuth's ranges through c = 10<sup>11</sup>

Knuth observed that, for 1 ≤ c ≤ 10<sup>9</sup>, the one-based rows
s(c) = q<sub>c−1</sub> + 1 satisfy

s(c) ∈ [c/φ − 3, c/φ + 5] ∪ [cφ − 2, cφ + 1].

The scanner `src/scan_bounds.c`, running the generator, checked this for
every 1 ≤ c ≤ 10<sup>11</sup> and found **no violations**. It also found
no violation of the stronger statement that every lower queen (s < c) lies
in the first interval and every upper queen (s > c) in the second.

The extreme deviations were

| Deviation | Extreme | Value | c | s(c) |
|---|---|---:|---:|---:|
| s − cφ (upper queens) | minimum | −1.380245390050 | 8996671875 | 14556920878 |
| s − cφ (upper queens) | maximum | 0.614522185168 | 38110513493 | 61664106161 |
| s − c/φ (lower queens) | minimum | −2.505950649811 | 59215597931 | 36597252183 |
| s − c/φ (lower queens) | maximum | 4.359904576102 | 4273570418 | 2641211776 |

The values are rounded to twelve places; the coordinates determine them
exactly. The columns comprise 61803398874 upper queens, 38196601125 lower
queens, and the origin. The last zero-based coordinate is
(99999999999, 61803398875), and the checksum of all 10<sup>11</sup> rows is
`6c1f1dc727d673bd`. This extends a finite check; it does not prove Knuth's
ranges for all c.

**Exact comparisons.** Writing the deviations as

2(s − cφ) = 2s − c − c√5,  2(s − c/φ) = 2s + c − c√5,

every comparison, whether of a deviation with an interval end or of two
deviations on the same side, is the sign of a − b√5 for integers a, b. The
scanner first uses double-precision arithmetic, with a proved bound on its
rounding error for c ≤ 10<sup>11</sup>. When that bound does not decide the
comparison (136589 times in this scan), it compares a² with 5b² exactly in
128-bit integers after checking signs (`src/bounds_exact.h`). The printed
decimal values come with an error bound below 1.05 × 10<sup>−12</sup>.

**Run.** The scan took 664.77 s of elapsed time, single-threaded and not
pinned, on 24 September 2026, on a desktop computer with an AMD Ryzen 7
3700X and 32 GiB of memory, under WSL with Ubuntu 20.04.1 and GCC 9.4.0,
built with `make build/scan_bounds` (the default flags above and `-lm`). At
the end the generator had 46 levels and 3704 bytes of heap, besides its
34925 bytes of fixed data; the scanner adds an 8192-byte buffer of rows.
This time includes the scan's own work, so it is not comparable with
the timing table.

**Checks.** `tests/check_bounds.py` compares the scanner's counts, extrema,
witnesses and checksum at fourteen counts up to 10<sup>6</sup> with an exact
Python scan of the rows printed by `knuth_packed`, and tests its exact sign
computation on 12289 cases and its comparisons on 24954 synthetic points
near the interval ends. `tests/check_bounds_results.py` rechecks the
recorded scan: the counts and monotone extrema in all 99 progress records
and the final one, every printed deviation against a 70-digit computation,
and the last row and checksum at 10<sup>9</sup> and 10<sup>10</sup> queens
against the EC2 runs of the timing table, which were made on another machine with
another compiler.

## Records

| File | Contents |
|---|---|
| `results/ec2-native.json` | All 40 runs of the campaign behind the timing table |
| `results/ec2-native.csv` | Medians and ranges of elapsed and processor time |
| `results/ec2-environment.json` | The EC2 machine, recorded separately |
| `results/ec2-validation.json` | The checked summary, including the medians of peak memory |
| `results/knuth-bounds-1e11.json` | The final record of the scan |
| `results/knuth-bounds-1e11-progress.log` | A record every 10<sup>9</sup> columns |
| `results/knuth-bounds-1e11-environment.json` | The scan's machine, compiler, command and time |
