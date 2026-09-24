# OEIS consequences (Section 6.5)

These programs check the statements about related OEIS sequences in
Section 6.5 of the paper: the corollary "Column runs and gaps" and the
statements that follow it about the gap sequence A275888. Appendix A
describes the same checks. None of this is needed for the main theorem.

Every program is plain Python (3.10 or later, standard library only) and
builds on the verification programs in `../verification`: the calculation
(`calculation.py`), the exhaustive check (`verify_tuples.py`), the
construction of history graphs (`construct_history_graph.py`), and the
direct greedy computation (`greedy.py`).

## Running the checks

From the repository root:

```sh
python oeis/run_all.py
```

or, from this directory, `python run_all.py`. This runs every check below
in order, writes its results to `results/`, and prints one `PASS` line per
verified statement, ending with `ALL CHECKS PASSED`. A failed check stops
with `FAIL` and a message. It takes about 40 seconds, most of it
constructing the forty-symbol history graph.

The programs can also be run one at a time, in either directory:

| Command | Checks | Time |
|---|---|---|
| `python graphs.py` | Constructs the forty-symbol history graph and explores both state graphs | 30 s |
| `python runs_and_gaps.py` | Upper bounds of the corollary "Column runs and gaps"; forbidden gap factors | 3 s |
| `python return_words.py` | The 156 return words to 3; the 63 faithful words | 3 s |
| `python four_gaps.py` | Minimum distance 71 between consecutive 4s; its unique fill | 3 s |
| `python witnesses.py` | Occurrence witnesses in the actual queens | 10 s |

Each program constructs the forty-symbol history graph if
`results/history-40.json` is missing (another 25 s), and otherwise reuses
it. Reusing it is safe, because the graph is checked in full every time it
is loaded (see below).

## What is proved, and how

Each statement has two halves. A finite graph derived from the verification
contains the actual sequence as one of its walks, so a property of all
walks is an *upper bound* for the actual sequence. The graph can also
contain walks that never occur, so it cannot show that a value is
*attained*; that comes from *witnesses*, occurrences in actual greedy
queens. The columns before a graph applies are checked directly in the
actual queens.

### Two state graphs

The twelve-symbol state graph is that of the finite verification of Section 6.3: the history graph
`../verification/history.json`, explored from the state before column 30.
It has 2092 history vertices and 2603 history edges, and 7014 states and
8327 state edges.

The twelve-symbol graph is too coarse for some of the statements, so the
verification is repeated with histories of length 40. Keep the records
w, z, R, D, A, Q, the bounds of Section 5.1, and the calculation of Section 4.5, but let
`H_in` and `H_out` hold the last 40 symbols instead of 12. The history graph
then has words of length 40 as vertices. The construction of Section 6.2,
with length 40, starting from the windows of sigma_1 ... sigma_79, closes
after twenty explorations with 16876 vertices and 17499 edges. With this
graph held fixed, the exhaustive check of Section 6.3 from the state before
column 80 reaches 29267 states and 30000 state edges. Every output check
passes, every successor satisfies the bounds of Section 5.1, and no request meets a
vertex without outgoing edges.

The induction of Section 6.4 then applies to the forty-symbol graph, so the
actual process is a walk in it from column 80 on. Two points need checking.

* **The start.** Immediately before column 80, the actual board has
  m = 51, d = 32, U(m-1) = 31, w = -3, z = -2, and R = D = A = empty.
  The input history holds sigma_11 ... sigma_50, the queue
  sigma_51 ... sigma_79, and the output history sigma_40 ... sigma_79, so
  every stored index is positive. The word sigma_1 ... sigma_79 follows the
  graph, and every lower queen before column 80 has |d_j - j| <= 4.
* **The lemma of Section 5.2 with longer histories.** The only part of its proof that
  depends on the history length concerns information left out of the
  records. An upper column omitted from a forty-symbol history has offset
  at most -41, which is further in the past than the offsets at most -13
  omitted from twelve-symbol histories, so the inequalities in the proof
  that exclude old row and antidiagonal attacks still hold. Keeping more
  old symbols never omits a relevant source. Requests still end by m + 6,
  and n - m = U(m-1) + z >= 12 - 4 = 8, so every requested symbol is already
  part of the actual word. So the hypothesis of the lemma remains
  U(m-1) >= 12, not U(m-1) >= 40, and it holds from column 80 on because
  the least unused row never decreases.

The extra symbols only strengthen the constraints from the past; they do
not widen the range of fresh inputs.

### Derived graphs

The output symbol of a state edge S -> S' taken before column n + 1 is
sigma_n, the last symbol of S'.H_out, and its upper-column bit
u_n = [q_n > n] is sigma_n >> 1.

* **The gap graph.** Its vertices are the states immediately after an
  upper column. Following lower outputs from such a state to the next upper
  output, k steps later, gives an edge labeled k. On the actual walk, the
  labels are the gaps between upper columns, the terms of A275888, from
  column 79 on. Four lower outputs in a row are an error; they never occur.
* **The run graph.** A gap k > 1 between upper columns encloses a lower
  run of length k - 1, and a unit gap encloses none. Following unit-gap
  edges from a gap-graph vertex and then one edge labeled k > 1 gives a
  run-graph edge labeled k - 1. On the actual walk, the labels are the
  lengths of the maximal lower runs, the terms of A275885. Five unit gaps in
  a row are an error; they never occur.

Each computation below is exact: it follows every edge of the graph, and
none is ever removed to obtain a desired answer.

### Column runs and gaps (Section 6.5)

*Upper bounds* (`runs_and_gaps.py`). Project each symbol of the queen word
to its upper-column bit. By the induction of Section 6.4, every twelve
consecutive symbols sigma_i ... sigma_{i+11} with i >= 1 form a vertex of
the twelve-symbol history graph, and no projected vertex contains `0000` or
`111111`. So lower runs have length at most 3, upper runs at most 5, gaps
between upper columns at most 4, and gaps between lower columns at most 6.

For A275887, the run lengths of equal terms of A275885, use the
forty-symbol run graph. For c = 1, 2, 3, the edges labeled c form an
acyclic graph. Let E(v) be the set of numbers of c-edges that can follow v
before the first edge with another label:

    E(v) = {0 if an edge with a label other than c leaves v}
           ∪ {1 + l : v --c--> t, l in E(t)}.

Reverse topological order computes these finite sets exactly. A maximal run
of c's starts at the target of an edge with another label, so the possible
lengths L_c are the nonzero elements of E(v) for those vertices:

    L_1 = {1, ..., 9, 11},   L_2 = {1, ..., 6},   L_3 = {1}.

Both boundaries matter: a run of eleven 1s contains ten consecutive 1s,
but they do not form a maximal run. With the twelve-symbol graph the same
calculation gives L_1 = {1, ..., 11}, so it cannot exclude 10.

*Witnesses and the start* (`witnesses.py`). In the first 20000 queens,
every value in the table of the corollary "Column runs and gaps" occurs, and each L_c is attained
by runs of c's. The origin, which these OEIS sequences count as an upper
column, is covered by the same direct check. A maximal run of equal terms
of A275885 is covered by the run graph when the edge of the unequal term
before it lies on the walk from column 80. The other runs, eleven in all,
are checked directly; determining that they are maximal needs the columns
through 95.

| Sequence | Statistic | Values |
|---|---|---|
| A275885 | Lower-column run lengths | 1, 2, 3 |
| A275886 | Upper-column run lengths | 1, ..., 5 |
| A275887 | Run lengths of equal terms in A275885 | 1, ..., 9, 11 |
| A275888 | Gaps between upper columns | 1, 2, 3, 4 |
| A275889 | Gaps between lower columns | 1, ..., 6 |

### The gap sequence A275888

Write g for A275888. A gap word c_1 ... c_r is the column pattern
`1 0^(c_1-1) 1 ... 1 0^(c_r-1) 1`.

*Forbidden factors* (`runs_and_gaps.py`). The column patterns of `11111`,
`2222`, `33`, `44`, and `3213` have at most twelve columns, and none occurs
in a projected vertex of the twelve-symbol history graph. The factors that
involve the origin are checked in the actual prefix (`witnesses.py`). In
particular, `213` is not a return word to 3.

*Return words to 3* (`return_words.py`). Cutting g after each 3 gives the
return words to 3. In the forty-symbol gap graph, let T be the set of
targets of edges labeled 3. The edges not labeled 3 that are reachable from
T form an acyclic graph, so the language

    W(v) = {3 : v --3--> t} ∪ {k w : v --k--> t, k ≠ 3, w in W(t)}

is finite. It is computed exactly in reverse topological order, recording
for each word the set of vertices where it can end. The words of W(v) for
v in T are exactly the 156 words of the catalogue
[`a275888-return-words.txt`](a275888-return-words.txt). Their lengths range
from 2 to 26, and exactly five contain a 4. The twelve-symbol gap graph
permits 247 return words, up to length 29, so the longer histories are
needed here.

*Faithful words* (`return_words.py`). Every actual successor of a return
word w belongs to the union Succ(w) of W(e) over the endpoints e of w. For
exactly 63 words, Succ(w) has a single element, so these words are
faithful. A path in the graph need not be actual, so a larger Succ(w) does
not show that w is not faithful. Instead, `witnesses.py` finds two
different actual successors for each of the other 93 words.

*Consecutive 4s* (`four_gaps.py`). The first 4 is the gap from column 4969
to column 4973, at index 3073, well after column 80, so every pair of
consecutive 4s is a path in the forty-symbol gap graph from the target of a
4-edge to the next 4-edge. Breadth-first search gives the minimum distance
71, measured in terms of g, not in columns. Listing every path of that
length gives a single fill, both 4s included:

    412111311132211131113221211223111122311112321113113112321113121212112214

*Witnesses and the start* (`witnesses.py`). A million queens, 618034 terms
of g, are generated by a program that uses the lemma of Section 2 and agrees with the
bitboard computation on its first 200000 queens. Every catalogue word
occurs, the last one (`11122211221223`) at indices 108002 to 108015. Each
of the 93 words that are not faithful has two different successors, all
found by index 573517. Every return word in the prefix, and every pair of a
word and its successor, is permitted by the graph; this covers the nine
words whose preceding 3 starts before column 79, where the gap graph does
not yet apply. Consecutive 4s at indices 83418 and 83489 attain the
distance 71.

The five words containing a 4 first occur at these indices of g:

| Word | Indices |
|---|---|
| `112112214121212121122123` | 3065–3088 |
| `121212112214121113` | 4971–4988 |
| `1112112214121113` | 7253–7268 |
| `1112212141211113` | 15750–15765 |
| `11212112214121212121122123` | 51583–51608 |

### What is not proved

The forty-symbol gap graph contains a cycle avoiding 4 that is reachable
from a 4 and from which a 4 can be reached. Going around it repeatedly gives
arbitrarily long paths between consecutive 4s, so the graph gives no upper
bound for their distance, and it cannot prove the proposed maximum distance
24853. This is not a counterexample: the actual sequence is one walk, and
not every walk is actual. Nor do these graphs determine the number of fills
at longer distances, limiting frequencies, or the mean distance between 4s.
A stronger abstraction, for instance histories that also record information
about returns to 4, justified by the same unrestricted construction and
check, would be needed. [`AUDIT.md`](AUDIT.md) goes through the related
OEIS entries one by one.

## Files

| File | Purpose |
|---|---|
| `run_all.py` | Runs every check and prints the summary |
| `graphs.py` | The two state graphs, the start before column 80, the gap graph, and the run graph |
| `runs_and_gaps.py` | Upper bounds of the corollary "Column runs and gaps" and the forbidden gap factors |
| `return_words.py` | The return-word language, the catalogue comparison, and the faithful words |
| `four_gaps.py` | Minimum distance between consecutive 4s, its fill, and the cycle avoiding 4 |
| `witnesses.py` | Two generators of actual queens and all occurrence witnesses |
| `a275888-return-words.txt` | Input: the 156 return words listed in the note linked from A275888 |
| `AUDIT.md` | What is proved, attained, and open for each related OEIS entry |

Outputs, written to `results/`:

| File | Contents |
|---|---|
| `history-40.json` | The forty-symbol history graph, in the format of `../verification/history.json` |
| `runs-and-gaps.json` | Sizes and labels of the gap and run graphs, and L_c for both history lengths |
| `return-words.json` | The 156 return words, Succ(w) for each, and the 63 faithful words with their successors |
| `four-gaps.json` | The minimum distance, its fill, and the labels of a cycle avoiding 4 |
| `witnesses.json` | First occurrences of every value, run length, word, and successor pair; the initial runs and words checked directly |
| `a275888-prefix.txt` | The first 618034 terms of A275888, as one line of digits |

In `witnesses.json`, columns are zero-based and indices of OEIS terms
one-based, and, as in the OEIS entries, the origin counts as an upper
column.

## Scope

This is a computer-assisted proof in the same sense as the finite verification of Section 6.3. The
graphs are checked by the programs of `../verification`, which are not
formally verified, and the passage from twelve to forty symbols rests on
the argument above. The witnesses are finite computations of actual
queens, checked by two separate generators.
