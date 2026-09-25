# Greedy Queens and the Golden Ratio: companion code

Place a queen in each successive column of an infinite chessboard, always in
the lowest row where no earlier queen attacks it. The paper *Greedy Queens
and the Golden Ratio* by Boon Suan Ho proves that the queen in column *n* lies
within a bounded distance of row *nφ* or of row *n*/*φ*, where
*φ* = (1 + √5)/2 is the golden ratio.

The proof reduces the theorem to a finite computation, and the paper also
uses that computation to answer questions from the OEIS and to generate the
sequence quickly with little memory. This repository contains all of that
code, organised by the part of the paper it supports. Each folder has its
own README with commands, expected output, and a map from files to sections
of the paper.

| Folder | Paper | What it contains |
|---|---|---|
| [`verification/`](verification/) | Sections 4–6, Appendix A | The local calculation, the history graph, and the exhaustive check behind the main theorem |
| [`oeis/`](oeis/) | Section 6.5, Appendix A | The finite graphs and witnesses behind the consequences for related OEIS sequences |
| [`fast_generator/`](fast_generator/) | Section 7, Appendix A | A C11 program that generates the sequence in linear time and logarithmic memory, with its measurements |

## Quick start

The Python programs need Python 3.10 or later and nothing else.

```sh
python verification/verify_tuples.py    # the exhaustive check of Section 6.3 (a few seconds)
python verification/trace.py 41 44      # the actual local states, column by column (Section 4.6)
python oeis/run_all.py                  # the checks behind Section 6.5 (under a minute)
```

The generator needs a C11 compiler and `make`:

```sh
cd fast_generator
make
./build/queens_fast --count 1000000     # the first million rows, with a checksum
make verify && make test                # its finite checks (about ten seconds)
```

## Where to start, depending on what you have read

- **Section 4 (the local state and the calculation).** Run `verification/trace.py`
  on a few columns and compare its output with the examples of Section 4.6.
  Then read `verification/calculation.py`, which follows Section 4.5 and
  Algorithm 1 step by step.
- **Sections 5 and 6 (the proof).** Run the five commands in
  [`verification/README.md`](verification/README.md). `verify_tuples.py` is
  the finite check of Section 6.3; `verify_bitmasks.py` repeats it
  independently.
- **Section 6.5 (OEIS consequences).** See [`oeis/README.md`](oeis/README.md).
- **Section 7 (fast generation).** See
  [`fast_generator/README.md`](fast_generator/README.md).

## License

The code is released under the MIT License; see [LICENSE](LICENSE). The
comparison program `fast_generator/knuth/knuth_packed.c` contains code taken
from Donald Knuth's program `infty-queens`, which remains his; see
[`fast_generator/README.md`](fast_generator/README.md#the-knuth-comparator).

## Notation used in the code

The code uses the notation of the paper. A *symbol* of the queen word is
2*u* + *b*, where *u* = 1 when the column contains an upper queen (above the
main diagonal) and *b* = 1 when the row does. A local state is the tuple
(*w*, *z*, *R*, *D*, *A*, *H*<sub>in</sub>, *Q*, *H*<sub>out</sub>) of
Section 4.2. Offsets are measured from the least unused row *m*.
