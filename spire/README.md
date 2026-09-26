# Spire

Place a queen in each column of an infinite chessboard, one column after another, always in the
lowest row that no earlier queen attacks. The paper studies the row q<sub>n</sub> of the queen
in column n and proves that it is always close to nφ or to n/φ, where φ is the golden ratio.
Spire computes these rows, exactly, and fast:

- **All the rows up to N.** On an 8-core desktop, the first 10<sup>10</sup> rows take 0.04
  seconds (and writing every one of them to memory 0.57 seconds); on a 16-core server, the first
  10<sup>12</sup> take under a second. Memory stays at a few megabytes however large N is.
- **Any stretch of rows**, written out as text or binary, from anywhere in the sequence.
- **A single row, on its own.** q<sub>n</sub> can be computed without any of the rows before it,
  in time proportional to the number of digits of n: q<sub>10<sup>100</sup></sub> takes 9
  milliseconds, and q<sub>10<sup>1000</sup></sub> a tenth of a second.

For example, the queen in column 10<sup>100</sup> is in row

    16180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911375

which is 10<sup>100</sup>φ + 0.152…: the first hundred digits of the golden ratio, read off a
chessboard.

Spire is not part of the paper. It is the generator of the paper's Section 7, reorganized for a
modern processor: it uses that generator's tables (in [`../fast_generator`](../fast_generator/))
and checks itself against that generator's rows.

**Contents:** [Running it](#running-it) · [Results](#results) · [How it works](#how-it-works) ·
[What is proved, and what is checked](#what-is-proved-and-what-is-checked) ·
[Discussion](#discussion) · [Files](#files)

## Running it

It needs a 64-bit processor, a C compiler with OpenMP and Python 3:

- **Linux:** GCC (or clang with libomp), on x86-64 or ARM64.
- **macOS:** Apple's clang with Homebrew's OpenMP (`brew install libomp`), on Apple Silicon
  or Intel.
- **Windows:** MSYS2, in the UCRT64 shell
  (`pacman -S make mingw-w64-ucrt-x86_64-gcc mingw-w64-ucrt-x86_64-python`).

```sh
make          # builds the four programs into build/ (a few seconds)
make check    # compares them with the Section 7 generator (under a minute)
```

The four programs:

| Program | What it does | Example |
|---|---|---|
| `spire N` | The first N rows, as a checksum (the fastest way to make them) | `build/spire 1e10` |
| `spire-rows N` | The same, writing every row to memory | `build/spire-rows 1e10` |
| `spire-print A B` | The rows q<sub>A</sub> … q<sub>B−1</sub>, to standard output | `build/spire-print 0 20` |
| `spire-at n …` | Single rows q<sub>n</sub>, each computed on its own | `build/spire-at 10^100` |

Numbers may be written out, or as `1e10` or `10^10`. Columns go up to 10<sup>19</sup> (where the
rows reach 1.6 × 10<sup>19</sup>, near the top of 64 bits), except in `spire-at`, which works
with numbers of any size up to about 10<sup>1150</sup>.

**`spire` and `spire-rows`** take `N [threads] [ranges]` and print one line of JSON:

    {"N":10000000000,"threads":16,"ranges":64,"last":16180339886,"poly63":"268175a70febc7ec","slow_steps":630,"setup":0.007,"seconds":0.041,"peak_mib":18.3}

`last` is the last row, q<sub>N−1</sub>. `poly63` is a checksum of all the rows,
H = Σ q<sub>n</sub> P<sup>N−1−n</sup> mod 2<sup>64</sup> with the prime P = 1099511628211,
reported modulo 2<sup>63</sup> (see "Hashing a step's rows at once"); `make check` computes the
same number directly from the rows of the Section 7 generator. `spire-rows` also reports
`rows_sum`, the sum of the rows it wrote (mod 2<sup>64</sup>). Then come the number of
`slow_steps` (see "Exact tables"), the time spent building the tables (`setup`) and in all
(`seconds`), and the peak physical memory (`peak_mib`).

**`spire-print A B`** writes q<sub>A</sub>, …, q<sub>B−1</sub> to standard output, one decimal
number a line (line i is q<sub>A+i</sub>), or with `--binary` as 64-bit little-endian numbers.
B may be written `+k`, for A + k, and an optional last number sets the threads:

```sh
build/spire-print 0 1e9 > rows.txt                 # the first 10^9 rows (10 GB)
build/spire-print 10^18 +1e6 --binary > far.bin    # a million rows from q_(10^18) on
build/spire-print 0 1e12 | ./my-analysis           # 10^12 rows, straight into a program
```

When it is done it prints a summary to standard error: the checksum, the sum and the last of the
rows it wrote (as `spire` and `spire-rows` report them), and the time.

**`spire-at n …`** prints a line of JSON for each n:

    {"n":1000000000000000000,"q":1618033988749894848,"near":"n*phi","deviation":-0.204587,"seconds":0.001356}

`near` says whether the queen is an upper one (q<sub>n</sub> > n, and then q<sub>n</sub> is near
nφ) or a lower one (near n/φ), and `deviation` is q<sub>n</sub> − nφ or q<sub>n</sub> − n/φ. With
`-` it reads the columns from standard input, and it computes many rows on all threads.

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

AWS `c8a.4xlarge` (AMD EPYC 9R45, Zen 5, 16 cores), Ubuntu 24.04, GCC 13.3, assembly loops,
rows written with AVX-512, all threads, setup included:

| N | `spire` | `spire-rows` |
|---|---|---|
| 10<sup>9</sup> | 0.017 s | 0.035 s |
| 10<sup>10</sup> | 0.020 s | 0.24 s |
| 10<sup>11</sup> | 0.10 s | 2.2 s |
| 10<sup>12</sup> | 0.96 s | 23 s |

Writing the rows with AVX-512 rather than AVX2 saves 7 to 13% here (`spire-rows` takes 26 s at
10<sup>12</sup> with AVX2), and 20% on an Intel Xeon 6975P-C (`c8i.4xlarge`, 8 cores with 2
threads each: 0.50 s rather than 0.62 s at 10<sup>10</sup>). On AMD Zen 4 (`c7a.4xlarge`, 16
cores: 0.32 s at 10<sup>10</sup>), which carries out each 512-bit instruction in two halves, it
makes no difference.

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

**Writing the rows out.** On the Ryzen, writing to the null device, `spire-print` makes the first
10<sup>9</sup> rows in 1.2 s as text (10 GB) and in 0.87 s as binary (8 GB), and 10<sup>9</sup>
rows from 10<sup>15</sup> on in 2.3 s as text (17 GB): several gigabytes a second, so in
practice the disk, or the program reading the rows, sets the pace. Its memory is fixed, however
long the stretch: about 100 MiB with 16 threads (150 MiB for rows of 16 digits), most of it
output waiting its turn to be written.

**Single rows.** One core of the Ryzen, one row:

| n | 10<sup>6</sup> | 10<sup>9</sup> | 10<sup>12</sup> | 10<sup>19</sup> | 10<sup>50</sup> | 10<sup>100</sup> | 10<sup>200</sup> | 10<sup>500</sup> | 10<sup>1000</sup> |
|---|---|---|---|---|---|---|---|---|---|
| `spire-at` | 0.17 ms | 0.44 ms | 0.81 ms | 1.4 ms | 4.5 ms | 9.0 ms | 19 ms | 47 ms | 98 ms |

The time grows with the number of digits of n, about 0.09 ms a digit. On all threads,
100 000 random rows between 10<sup>18</sup> and 10<sup>19</sup> take 12 seconds.

## How it works

Spire is the paper's generator (Section 7), reorganized. The generator is a chain of copies of
one small calculation, each feeding the next; the first part below explains it, since everything
else builds on it. Spire then changes three things:

1. **It starts the chain anywhere.** Each thread can then take its own range of columns, and a
   single row can be computed without the rows before it.
2. **It merges several copies into one machine**, a "tower", so that one table lookup makes
   about 190 rows instead of about 6.
3. **It suits the work to the processor**: exact tables that fit the fast caches, the checksum
   of a step's rows in two multiplications, and inner loops that keep the processor busy while
   it waits for memory.

### The starting point: a calculation that reads its own output

Placed directly, each queen needs the whole board so far: the rows, columns and diagonals already
attacked. The paper shows (Sections 4 and 7) that far less is needed. Record, for each index i,
whether column i and row i hold an upper queen (a queen above the diagonal, q<sub>i</sub> > i);
this gives a symbol σ<sub>i</sub> ∈ {0, 1, 2, 3}, and the sequence σ = σ<sub>1</sub>σ<sub>2</sub>…
is the *queen word*. To place the queen in column n, the calculation needs a bounded amount of
state and the queen word near index m, the lowest row not yet used. As m ≈ n/φ, the calculation
that places the queens near column n, and writes σ<sub>n</sub>, reads σ only far behind, near
n/φ.

So the queen word can make itself. A second copy of the same calculation, working near column
n/φ, makes the symbols the first one reads; a third copy near n/φ<sup>2</sup> makes those the
second reads; and so on, down to the first 29 columns, which are placed directly:

```
   seed ──► copy k ──► ··· ──► copy 2 ──────► copy 1 ──────► copy 0 ──────► rows q_n
                               writes σ       writes σ       places the queens
                               near n/φ²      near n/φ       near column n
```

Each copy holds only a small state and a short buffer, and the chain has about log<sub>φ</sub> N
copies, so the memory is logarithmic in N. The paper compiles one copy into a table: between
input bytes, a copy's state is one of 82 *classes*, and one lookup reads a byte (four symbols of
σ) and writes 3 to 12 symbols (or, for copy 0, places 3 to 12 queens), about 6.5 on average,
since a copy writes φ symbols for each one it reads.

### Starting a copy anywhere

The chain looks sequential: copy 0's state at column n depends on everything before it. That
would rule out two things Spire wants: letting each of 16 threads take its own range of columns,
and computing a row without the rows before it. The way out is that a copy's state can be found
from a short look at its input.

Between two input bytes, a copy's state (with the few symbols it is holding) is one of 300
*paused records* (Section 7.3). To find which, take the 128 input symbols just before the point:
start with all 300 records as candidates, follow each through those symbols, and drop any that
cannot read the next one. The true record can always read the actual input, so it is never
dropped; when one candidate is left, it is the true record. And one is always left within 58
symbols, a fact proved by a finite computation (see "What is proved").

A record does not contain the copy's counters (its column n, the lowest unused row m, and the
number U of upper queens so far), which grow without limit. But the paper's identities give
them from the record and the input position p:

    m = p − |Q|,    n = m + U(m − 1) + z,    U(n − 1) = m + w − |D|,

where |Q|, z, w and |D| are small numbers stored in the record, and U(m − 1) comes from the copy
below, which knows how many upper symbols it has written up to p.

To start copy 0 at column A, then: copy 0 reads its input near A/φ, so start copy 1 a little
before that; copy 1 reads near A/φ<sup>2</sup>, so start copy 2 there; and so on, until a
column is small enough to start from the seed. Each copy reads its 128 symbols, finds its
record, and walks a few hundred columns forward to exactly where the copy above needs it. For
A = 10<sup>10</sup> that is about 28 copies and a fraction of a millisecond. So Spire splits
the N columns into ranges (64 by default), starts a chain at the beginning of each, runs them
on all threads, and combines the ranges' checksums at the end. The threads share nothing but the
tables.

### One row, without the rows before it

Starting anywhere has a surprising consequence: q<sub>n</sub> can be computed on its own. Start
a chain at column n, as above, and read the row that copy 0 places there. Only a short piece of
σ is ever made at each level, near n/φ, near n/φ<sup>2</sup>, and so on: about log<sub>φ</sub> n
pieces of a few hundred symbols each. No row before q<sub>n</sub> is made, or needed.

Why is this possible? The calculation looks back only a bounded distance, at a point φ times
closer to the start, and between input bytes it forgets everything but one of 300 records,
which the recent input determines. So the row at column n depends on the queen word only near
n/φ, n/φ<sup>2</sup>, …, and each of those short pieces can be made from the pieces below it.
The counters, the only quantities that remember the whole past, follow from the identities.

`spire-at` does exactly this, with nothing else: single copies, each started at its record from
128 symbols of the copy below, down to a prefix of σ made directly (`spire-at.c` is short, and
reads as this section does). The numbers are as large as n, but a copy only ever compares them,
moves them by small amounts, or divides them by φ, so they are kept as integers of up to 64
words, and 1/φ is computed to 4 224 bits when the program starts, from the integer square root
of 5. For n = 10<sup>100</sup> the chain has about 460 copies, and the row takes 9 ms.

The rows it finds show the paper's theorem at sizes no one could reach one row at a time.
Section 6 proves that

    1 − 4/φ < q_n − nφ < 2/φ          (−1.472 to 1.236)   if q_n > n,
    −2 − 4/φ < q_n − n/φ < 4 + 1/φ    (−4.472 to 4.618)   if q_n < n.

Among 100 000 random columns between 10<sup>18</sup> and 10<sup>19</sup>, 61.9% of the queens are
upper (1/φ = 61.8%), their deviations running from −0.760 to 1.230, and the lower ones from
−2.888 to 3.976; `make check` checks rows up to 10<sup>1000</sup> against these bounds.

### Towers: many copies in one lookup

Once a chain is started, running it is a matter of table lookups: copy 0 reads a byte and places
about 6.5 queens, copy 1 reads a byte for every 6.5 symbols copy 0 reads, and so on. Each lookup
must wait for the one before it, since the next class is in the entry, and a lookup that hits
the processor's fast cache takes about 15 cycles. Counting every copy, a chain makes 1/(4φ) +
1/(4φ<sup>2</sup>) + … = φ/4 ≈ 0.4 lookups a row. To go faster, each lookup must make more rows.

The idea is to treat two consecutive copies as one machine:

```
   one input byte ──► copy 1: one step, writes 3 to 12 symbols
                                  │
                                  ▼
                      the symbols waiting from before (0 to 3), then the new ones
                                  │
                                  ├──► every whole byte (4 symbols) ──► copy 0: 0 to 3 steps
                                  │
                                  └──► what is left (0 to 3 symbols) waits for the next byte
```

The pair's state is copy 1's class, copy 0's class, and the 0 to 3 symbols waiting between them
(copy 0 reads whole bytes, so up to three symbols can wait). Reading one input byte, the pair
steps copy 1 once and copy 0 as far as it can. So the pair is again a machine that reads a byte
and writes symbols, or rows, only more of them: about 4φ<sup>2</sup> ≈ 10.5 per byte. Stacking
k copies the same way gives a *tower* of height k, which makes about 4φ<sup>k</sup> per lookup.

A tower's possible states multiply with its height: 82 classes for each copy, and 85 ways for
each group of waiting symbols. But the queen word is so regular that very few of them ever
occur. Along its first 2<sup>24</sup> symbols, the transitions a tower meets are:

| copies in the tower | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| transitions | 813 | 8 195 | 13 451 | 17 654 | 20 340 | 21 963 | 22 930 | 23 522 |

Each copy added makes a lookup worth φ times more rows, while the table grows less and less. So
Spire puts a tower of 8 copies on top of the chain: one lookup, about 190 rows, and 53 million
lookups for 10<sup>10</sup> rows instead of 4 billion. Below the top, the chain has little to do
(one byte for every 190 rows), and towers of 2 copies ("pairs"), whose small table stays in the
fastest cache, suit it best.

### Exact tables

Which transitions should the tables hold? Spire runs each tower along the first 2<sup>24</sup>
symbols of σ and keeps the transitions it meets: the *plan* (`build/plan.h`, which `make`
computes in under a second). The tables hold exactly these, packed densely so that the busy part
stays in the fast cache, and at startup every entry is computed from the Section 7 table.

The plan is a sample, and a run may meet a transition it lacks. So every slot is tagged with the
state it belongs to, and a lookup checks the tag. A mismatch is a transition the plan never met,
and it is computed from the Section 7 table on the spot (the "slow path"), so the result is
exact whatever the input. At N = 10<sup>10</sup> this happens 630 times, among 53 million steps.

### Hashing a step's rows at once

To check its output without keeping it, Spire folds the rows into the checksum H. Hashing them
one at a time would cost a multiplication a row, now more than the lookups cost. But the rows of
a tower step have a simple form: each is m + c or (n + U) + c, where m and n + U are the counters
before the step and c is fixed by the transition. So the whole step changes the checksum by a
formula,

    H ← H P^L + m A + (n + U) B + C,

where L is the step's number of rows and A, B and C are fixed by the transition, and stored in
its slot. Since (P − 1)(1 + P + … + P<sup>L−1</sup>) = P<sup>L</sup> − 1, the value
F = (P − 1) H + m obeys

    F ← F P^L + (n + U − m)(P − 1) B + (P − 1) C + dm,

two multiplications a step, however many rows the step makes. As P − 1 is even, F gives H only
modulo 2<sup>63</sup>, which is what Spire reports.

### Writing the rows

`spire-rows` and `spire-print` also write the rows. Each top transition keeps the list of copy
0's steps within it, and each of those gives its 3 to 12 rows (each m or n + U plus an offset)
with a few vector instructions: 8 rows an instruction with AVX-512, 4 with AVX2, 2 with NEON on
ARM64. The rows go to a buffer of 1024 rows, which is summed (and, for `spire-print`, turned
into text) whenever it fills. `spire-print` works through the stretch in pieces of four ranges
of 2<sup>17</sup> rows, on all threads, and writes the pieces in order.

### What the processor wants

After the towers, the time goes to chains of lookups, each address depending on the lookup
before, each waiting about 15 cycles for the cache. The inner loops are built around that wait:

- **Four chains at once.** Each thread runs four ranges side by side, so the processor always
  has an independent lookup to work on while the others wait.
- **Every chain in registers.** On x86-64, with its 16 general registers, the C compiler ran out
  of registers with four chains and kept parts of them on the stack, adding a store and a load
  to every step. There the loops are in assembly (`loops.S`), with registers assigned by hand,
  and the tables sit at fixed addresses (`layout.h`) so that an instruction can name a table as
  a constant. ARM64 has 31 registers, and the same loops in C (`loops.c`) need no such help.
- **Chains apart from their work.** A step's other work (packing its symbols, updating the hash)
  would fill the processor's schedulers while the chain waits. So one loop runs the four chains
  alone, recording each step's slot, and a second loop does the work from the records.
- **Small hot tables.** A chain step reads a 4-byte slot (the tag and the next state); the rest
  of the step's data is in separate tables at the same slot number.

## What is proved, and what is checked

Spire's results are proved, not only tested: given the paper and code that carries out the
steps described above, **every row Spire prints is right, and it always prints one.** The full
argument, with the time and memory of `spire-at`, is in [`spire-at.md`](spire-at.md). In
outline:

- The chain of copies computes the queen word and the rows, and the Section 7 table is a correct
  compilation of one copy (Section 7).
- Between input bytes a copy is always in one of the 300 paused records, and the record graph
  gives its moves (Sections 6 and 7).
- The identities m + |Q| = 30 + 4t, n = m + U(m − 1) + z (Section 7) and U(n − 1) = m + w − |D|
  (Section 6) hold at every pause, which gives the counters of a copy that is started.
- Finding a record is a deduction, not a guess: the true record is consistent with the actual
  input, so it is never dropped, and when a single candidate is left it is the true record.
- A single candidate is always left within 58 input symbols (Spire reads 128). This is a finite
  computation, [`synchronization.py`](synchronization.py), run by `make check`: the queen word
  follows the paper's forty-symbol history graph (Appendix A3), and along every path of that
  graph, from every state the process can reach, one record is left within 58 symbols.
- A copy started where Spire starts it is always 508 to 543 columns before its target, by the
  paper's bounds on U(x) − x/φ (Proposition 21), so it never starts too late.

That the code is right, `make check` tests:

- `spire`, `spire-rows` and `spire-print` against the Section 7 generator's rows, from 1 to
  10<sup>8</sup> rows, split between different numbers of threads and ranges, from the start and
  from inside the sequence, as text and as binary;
- `spire-at` against the Section 7 generator's single rows below 10<sup>7</sup>;
- beyond the reference, `spire-at` against `spire-print` up to 10<sup>19</sup>: two different
  programs, one with single copies and numbers of any size, the other with tower tables and
  64-bit numbers;
- `spire-print` against itself, with ranges that start elsewhere, and its checksum (from the
  hash formula) against the rows it wrote;
- beyond 10<sup>19</sup>, `spire-at` against itself with its chain aimed three different ways
  (`--walk D` starts it D columns early), and every row it finds, up to 10<sup>1000</sup>,
  against the bounds of Section 6.

## Discussion

About a fifth of `spire`'s time at 10<sup>10</sup> goes to building the tables (8 ms), and the
rest roughly evenly to the top tower and to the chains below it. `spire-rows` is limited by
writing the rows: about 2 processor cycles per row, where the hardware could store one row every
quarter cycle. The assembly is worth about a fifth of `spire`'s time on x86-64 (0.040 s against
0.050 s at 10<sup>10</sup>).

Some things did not help. A complete table of the two-copy towers (all 4782 states reachable
from the start) is 2 MB with its used entries scattered, and its lookups go to the slow third-level
cache. Taller towers than eight would need a wider row counter (a step of nine copies can make
78 732 rows) for little gain. And a loop bound by multiplications, like the checksum's, runs no
faster with two threads per core, which share one multiplier.

`spire-at` stops at about 10<sup>1150</sup> only because its integers have 64 words
(`BIG_WORDS`); with more, it reaches further, at a cost that grows a little faster than the
number of digits.

## Files

| File | What it is |
|---|---|
| `spire.c` | The program, with an overview of the ideas and a section for each |
| `spire-rows.c` | `spire.c` compiled to write every row |
| `spire-print.c` | `spire.c` compiled to write the rows out |
| `spire-at.c` | Single rows, with single copies and numbers of any size (uses the base table and records of `spire.c`) |
| `loops.S` | The four inner loops (chains, symbol packing, checksum) in x86-64 assembly, for Linux and Windows |
| `loops.c` | The same loops in C, for other processors and systems |
| `layout.h` | The fixed addresses of the tables, shared by the C and the assembly |
| `make_records.py` | Writes the record tables, checking the counter formulas along σ |
| `synchronization.py` | Proves that 58 input symbols always identify a copy's record (run by `make check`) |
| `spire-at.md` | Why `spire-at` is correct, and its time and memory |
| `reference.c` | The Section 7 generator's rows, with Spire's checksums and chosen single rows |
| `check.py` | The comparison run by `make check` |
| `Makefile` | Builds everything into `build/` |
