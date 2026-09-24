# The finite verification (Sections 4–6)

The main theorem rests on one bound, Lemma 5 of the paper: the *j*th lower
queen lies on a lower diagonal within 4 of *j*. Sections 4–6 prove it with a
finite computation and an induction. This folder contains that computation
and the programs that check it.

In outline:

- **Section 4** describes a *local state* of the board (eight records) and a
  *calculation* that turns the state before column *n* into the state before
  column *n* + 1. When it needs an earlier symbol of the queen word that it
  has not stored, it reads the possibilities from a fixed *history graph*.
- **Section 5** proves that, on the actual board, the branch of the
  calculation that reads the actual earlier symbols carries out the actual
  greedy step, provided the records satisfy some bounds.
- **Section 6** constructs the history graph, checks by computer that every
  state reached from the board before column 30 passes the output check and
  satisfies the bounds, and concludes by induction.

Everything here uses Python 3.10 or later and only the standard library.
Run the programs from this folder.

## Check the verification

```sh
python verify_tuples.py          # the exhaustive check of Section 6.3
python verify_bitmasks.py        # the same check, implemented independently
python compare_verifiers.py      # the two state graphs are identical
python check_correspondence.py   # the calculation matches 3000 actual queens
python test_rejection.py         # a graph with one edge removed is rejected
```

Each takes a few seconds. The first two print

```text
VERIFIED
history-graph vertices and edges: 2092 2603
state-graph vertices and edges: 7014 8327
completed choices: 7612
completed lower choices: 3153
...
requests with no outgoing edge: 0
```

and the tuple version also reports the largest fresh input offset (5), the
largest row advance (5), and the range of *w* − *r* − |*D*| at lower choices
([−4, 2]). These are the numbers in Proposition "Finite verification" and
Appendix A.

A successful run of `verify_tuples.py` establishes the finite statement of
Section 6.3. The infinite statement, that the actual queens follow the checked
states forever, is the induction of Section 6.4; `check_correspondence.py`
tests that identification on columns 30 through 2999 but does not replace it.

## Follow the actual queens

```sh
python trace.py            # columns 41 to 44
python trace.py 53         # one column
python trace.py 41 60      # a range
```

prints, for each column, the absolute values *m*, *d*, *U*(*m*−1), the eight
stored records, every request with the symbols the graph allows, the queen
chosen, the new symbol, and the advances *μ* and *ν*. Each step is checked
against the board computed directly from the greedy rule. Section 4.6 works
through columns 41, 42, 47, and 53 by hand; `trace.py` reproduces them.

## Construct the history graph

```sh
python construct_history_graph.py      # Section 6.2
python history_length_experiment.py    # histories of length 4 to 14
```

The first program starts from the windows of the first thirty queens and runs
the calculation, adding each missing output edge instead of failing, until a
complete pass adds nothing. It takes 14 passes and produces exactly
`history.json`. The proof does not depend on this: the verifiers check the
finished graph with no edges added.

The second repeats the construction with other history lengths. Lengths 4
through 11 reach a state violating the bounds of Section 5; lengths 12, 13,
and 14 close. So twelve is the shortest history that works with these records
and bounds.

Outputs are written to `results/`.

## Files

| File | Paper | Purpose |
|---|---|---|
| `greedy.py` | §1, §4.1–4.2 | The greedy queens, the queen word, and the records of the board, computed directly |
| `calculation.py` | §4.2–4.5 | Local states, the history graph, and the calculation (Algorithm 1) |
| `history.json` | §4.3, §6.2 | The history graph used in the proof |
| `verify_tuples.py` | §6.1, §6.3 | The exhaustive check, using `calculation.py` |
| `verify_bitmasks.py` | §6.3 | An independent implementation of the same check |
| `compare_verifiers.py` | App. A | Compares the two state graphs state by state |
| `actual_branch.py` | §5 | The branch that reads the actual earlier symbols, checked against the board |
| `check_correspondence.py` | §5, App. A | Runs that branch on columns 30–2999 |
| `trace.py` | §4.6 | Prints the actual steps column by column |
| `test_rejection.py` | App. A | Both verifiers reject a damaged graph |
| `construct_history_graph.py` | §6.2 | Builds the history graph |
| `history_length_experiment.py` | §6.2 | Repeats the construction with lengths 4–14 |

### The two verifiers

`verify_tuples.py` follows the paper closely: `calculation.py` stores the
eight records as a named tuple and implements Algorithm 1 with generators
that yield one result per branch: `extend_queue` for Extend, and
`choose_queen` and `find_free_row` for its two loops. `verify_bitmasks.py` shares no code with it. It
packs the records into integers, splits each symbol into its two bits, and
handles branching with explicit work lists. `compare_verifiers.py` converts
both to one encoding and compares every state and its complete set of
successors.

### The history graph file

`history.json` has the form `{"memory": 12, "vertices": [[h, mask], ...]}`.
Each record is one vertex: `h` is the twelve-symbol word in base four, with
the newest symbol as the last digit, and bit *s* of `mask` is set when an edge
labeled *s* leaves the vertex. A symbol is 2*u* + *b*, where *u* marks an upper
column and *b* an upper row.
