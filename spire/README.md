# Spire

Spire generates the greedy queen rows q<sub>0</sub>, q<sub>1</sub>, q<sub>2</sub>, … much
faster than the generator of Section 7, by reorganizing the same calculation for a modern
processor. It is exact, it uses every core, and like the Section 7 generator it needs only
logarithmic memory. On an 8-core desktop it makes the first 10<sup>10</sup> rows in 0.04
seconds; writing every one of them to memory as a 64-bit number takes 0.57 seconds.

Spire is not described in the paper. It builds on Section 7 (the chain of copies, the paused
records and the four-symbol table), using the tables of [`../fast_generator`](../fast_generator/)
and checking itself against that generator's rows.

## Running it

It needs a 64-bit processor, a C compiler with OpenMP and Python 3:

- **Linux:** GCC (or clang with libomp), on x86-64 or ARM64.
- **macOS:** Apple's clang with Homebrew's OpenMP (`brew install libomp`), on Apple Silicon
  or Intel.
- **Windows:** MSYS2, in the UCRT64 shell
  (`pacman -S make mingw-w64-ucrt-x86_64-gcc mingw-w64-ucrt-x86_64-python`).

On x86-64 with AVX2 and BMI2 (Intel since 2013, AMD since 2015), under Linux or Windows, the
inner loops are in assembly (`loops.S`). Everywhere else, and with `make PORTABLE=1`, they are
the same loops in C (`loops.c`).

```sh
make                              # build/spire and build/spire-rows (a few seconds)
make check                        # compare them with the Section 7 generator (a few seconds)
build/spire 10000000000           # the first 10^10 rows: checksum, time, memory
build/spire-rows 10000000000      # the same, writing every row to memory
```

Both take `N [threads] [ranges]` and print one line of JSON: `last` (the last row), `poly63`
(the checksum below), for `spire-rows` also `rows_sum` (the sum of the rows written, mod
2<sup>64</sup>), the number of `slow_steps` (see "Exact tables"), the time spent building the
tables (`setup`) and in all (`seconds`), and the peak physical memory (`peak_mib`).

The checksum is H = Σ q<sub>n</sub> P<sup>N−1−n</sup> mod 2<sup>64</sup>, with the prime
P = 1099511628211; Spire reports it modulo 2<sup>63</sup> (see "The rows' checksum").
`make check` computes it, and the sum of the rows, directly from the rows of the Section 7
generator for N from 1 to 10<sup>8</sup>, and compares.

## Results

AMD Ryzen 7 3700X (8 cores, 16 threads), Windows 10, GCC 12.2, all threads, setup included:

| N | Section 7 generator (1 thread) | `spire` | `spire-rows` |
|---|---|---|---|
| 10<sup>9</sup> | 2.7 s | 0.014 s | 0.10 s |
| 10<sup>10</sup> | 26.5 s | 0.040 s | 0.57 s |
| 10<sup>11</sup> | | 0.30 s | 5.6 s |
| 10<sup>12</sup> | | 2.9 s | 56 s |

Peak memory is about 20 MiB at every N up to 10<sup>12</sup>: each thread's chains of copies
take a few dozen kilobytes (logarithmic in N), and the tables about a megabyte. The checksums at
10<sup>10</sup>, 10<sup>11</sup> and 10<sup>12</sup> are `268175a70febc7ec`,
`2453193a2e8aae58` and `74986f235efafcda`. Under Linux (tested under WSL 1, which emulates it)
the results are the same and the times somewhat longer. On this processor the C loops
(`make PORTABLE=1`) take 0.050 s at 10<sup>10</sup>, and 0.60 s writing the rows.

AWS Graviton4 (Neoverse V2, 16 cores, `c8g.4xlarge`), Ubuntu 24.04, GCC 13.3, C loops, all
threads, setup included:

| N | `spire` | `spire-rows` |
|---|---|---|
| 10<sup>9</sup> | 0.008 s | 0.077 s |
| 10<sup>10</sup> | 0.020 s | 0.68 s |
| 10<sup>11</sup> | 0.14 s | 6.7 s |
| 10<sup>12</sup> | 1.3 s | |

The checksums are the same as on x86-64. ARM64 has 31 general registers, so there the C
compiler keeps all four chains in registers by itself (see "What the processor wants").

Apple M5 (4 performance and 6 efficiency cores, 24 GB), macOS 26.6, Apple clang 21.0 with
Homebrew's libomp 23.1, C loops, all 10 threads, the default 64 ranges, setup included:

| N | `spire` | `spire-rows` |
|---|---|---|
| 10<sup>9</sup> | 0.006 s | 0.085 s |
| 10<sup>10</sup> | 0.023 s | 0.80 s |
| 10<sup>11</sup> | 0.19 s | 8.0 s |
| 10<sup>12</sup> | 1.8 s | 85 s |

The checksums are again the same, and peak memory is 14 MiB (18 MiB for `spire-rows`). The two
kinds of core run at different speeds, so the longer runs gain from smaller pieces of work: with
160 ranges (`build/spire N 10 160`) they take 4 to 9% less (`spire` 1.7 s at 10<sup>12</sup>,
`spire-rows` 0.74 s at 10<sup>10</sup> and 77 s at 10<sup>12</sup>), while the shortest take a
little more (0.008 s at 10<sup>9</sup>: each range costs about 0.2 ms to start). The performance
cores alone are slower (2.5 s at 10<sup>12</sup> on 4 threads).

## How it works

The code is `spire.c`, whose comments walk through the ideas below in order. `loops.S` holds the
four inner loops in x86-64 assembly and `loops.c` the same loops in C, and `layout.h` says where
the tables live.

### A chain of copies, started anywhere

The Section 7 generator is a chain of copies of one calculation: copy 0 makes the rows, reading
the queen word σ; copy 1 makes the part of σ that copy 0 reads; and so on down to the seed. Each
copy is a small machine with 82 states (classes) that reads a byte (four symbols) and makes 3 to
12 symbols, or rows.

A chain is sequential, but a copy's state can be found from a short look at its input. Starting
from the set of all 300 paused records of Section 7.3 and reading the actual input symbols, the
inconsistent records drop out; in every test one was left within 43 symbols (Spire reads 128,
and stops with an error if more than one is left). A record gives the
copy's exact counters there (the least unused row m, the column n, and the number U of upper
columns so far):

    m = p − |Q|,    n = m + U(m − 1) + z,    U(n − 1) = m + w − |D|,

where p is the input position and Q, z, w, D belong to the record. `make_records.py` checks
these along half a million points of σ as it writes the record tables. So any copy can be started
anywhere: each thread builds its own chain for its own range of columns, and the ranges'
checksums are combined at the end.

### Towers: several copies in one lookup

Consecutive copies, each reading the one below, form a machine of the same kind: its state is
their classes and the 0 to 3 symbols pending between each two of them. Spire calls such a stack
a tower. One input byte steps the bottom copy once and every copy above it as far as it can go.
The chain below the top is made of towers of two copies; the top is a tower of eight, one step
of which stands for about 190 rows and 75 steps of the single copies.

Along σ very few of a tower's possible transitions occur, because σ is so regular. Along its
first 2<sup>24</sup> symbols:

| copies in the tower | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| transitions | 813 | 8 195 | 13 451 | 17 654 | 20 340 | 21 963 | 22 930 | 23 522 |

The tables grow less and less while each copy added divides the number of top steps by φ.

### Exact tables

Spire's tables hold exactly the transitions that occur along σ. `make` finds them (the "plan",
`build/plan.h`, in under a second) and packs them densely, and at startup every entry is
computed from the Section 7 table. The plan is a bet on the input, so every slot is tagged with
the state it belongs to. A lookup whose tag does not match is a transition the plan never met,
and it is computed from the Section 7 table on the spot: the result is exact whatever the
input. At N = 10<sup>10</sup> this happens 630 times.

### The rows' checksum

Each row of a top step is either m + offset or (n + U) + offset, with m and n + U taken before
the step and the offsets fixed by the transition. So a step changes the checksum by a formula,

    H ← H P^L + m A + (n + U) B + C,

L being its number of rows and A, B, C fixed per transition. Since
(P − 1)(1 + P + … + P<sup>L−1</sup>) = P<sup>L</sup> − 1, the value F = (P − 1) H + m obeys

    F ← F P^L + (n + U − m)(P − 1) B + (P − 1) C + dm,

two multiplications a step, however many rows the step makes. As P − 1 is even, F gives H only
modulo 2<sup>63</sup>, which is what Spire reports. `spire-rows` also writes the rows: each
transition keeps the list of its copy 0 steps, and each of those gives its 3 to 12 rows with a
few vector instructions, four rows at a time.

### What the processor wants

The inner loops are chains of table lookups, each address depending on the lookup before: each
step waits about 15 cycles for the cache.

- **Four chains at once.** Each thread runs four ranges side by side, so the processor always has
  an independent lookup to work on.
- **Every chain in registers.** On x86-64, with its 16 general registers, the C compiler ran out
  of registers with four chains and kept parts of them on the stack, adding a store and a load
  to every step. The loops there are therefore in assembly with registers assigned by hand, and
  the tables sit at fixed addresses so that an instruction can name a table as a constant.
  ARM64 has 31 registers, and the C loops need no such help.
- **Chains apart from their work.** A step's other work (packing its symbols, updating the hash)
  would fill the processor's schedulers while waiting for the chain. So one loop runs the four
  chains alone, recording each step's slot, and a second loop does the work from the records.
- **Small hot tables.** A chain step reads a 4-byte slot (the tag and the next state); the rest
  of the step's data is in separate tables at the same slot number.

## Discussion

About a fifth of `spire`'s time at 10<sup>10</sup> goes to building the tables (8 ms), and the
rest roughly evenly to the top tower and to the chains below it. `spire-rows` is limited by
writing the rows: about 2 processor cycles per row, where the hardware could store one row every
quarter cycle.

Some things did not help. A complete table of the two-copy towers (all 4782 states reachable
from the start) is 2 MB with its used entries scattered, and its lookups go to the slow third-level
cache. Taller towers than eight would need a wider row counter (a step of nine copies can make
78 732 rows) for little gain. And a loop bound by multiplications, like the checksum's, runs no
faster with two threads per core, which share one multiplier.

The assembly is worth about a fifth of `spire`'s time on x86-64 (0.040 s against 0.050 s at
10<sup>10</sup>). `spire-rows` writes its rows with AVX2 on x86-64 processors that have it,
and with NEON on ARM64.

## Files

| File | What it is |
|---|---|
| `spire.c` | The program, with an overview of the ideas and a section for each |
| `spire-rows.c` | `spire.c` compiled to write every row |
| `loops.S` | The four inner loops (chains, symbol packing, checksum) in x86-64 assembly, for Linux and Windows |
| `loops.c` | The same loops in C, for other processors and systems |
| `layout.h` | The fixed addresses of the tables, shared by the C and the assembly |
| `make_records.py` | Writes the record tables, checking the counter formulas along σ |
| `reference.c` | The Section 7 generator's rows, with Spire's checksums |
| `check.py` | The comparison run by `make check` |
| `Makefile` | Builds everything into `build/` |
