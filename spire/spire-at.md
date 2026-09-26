# Why `spire-at` is correct, and what it costs

`spire-at n` prints the row q<sub>n</sub> of the greedy queen in column n without computing the
rows before it. This note proves that it always prints a row, that the row is q<sub>n</sub>, and
analyses its running time and memory. It follows the program
[`spire-at.c`](spire-at.c) step by step, and rests on results of the paper, cited by number.

In short:

- **Correctness (Theorem 1).** If `spire-at` prints a row for n, the row is q<sub>n</sub>. This
  follows from the paper's results and the data of its Section 7 generator; no step is a guess.
- **It always prints (Theorem 2).** For every n up to the size of its integers (about
  10<sup>1156</sup>), `spire-at` prints a row. The one step that could have failed, identifying
  a copy's state from 128 of its input symbols, always succeeds: 58 symbols are enough (Lemma 6,
  proved by a finite computation in [`synchronization.py`](synchronization.py), from the
  paper's forty-symbol history graph).
- **Cost (Theorem 3).** It starts about log<sub>φ</sub> n copies of the calculation, each doing
  a bounded amount of work, so it takes O(log n) steps on numbers of O(log n) bits: O(log n)
  time on a machine whose words hold such numbers, O(log<sup>3</sup> n) bit operations as
  written. Computing the rows one after another instead takes time proportional to n.

**Contents:** [1. The setting](#1-the-setting) · [2. The facts used](#2-the-facts-used) ·
[3. The procedure](#3-the-procedure) · [4. Correctness](#4-correctness) ·
[5. It always prints](#5-it-always-prints) · [6. Time and memory](#6-time-and-memory) ·
[7. Checks](#7-checks)

## 1. The setting

The queen in column n sits in row q<sub>n</sub> (columns and rows start at 0). A queen is
*upper* if q<sub>n</sub> > n and *lower* otherwise. U(x) is the number of upper queens in
columns 1, …, x. The *queen word* is σ = σ<sub>1</sub>σ<sub>2</sub>…, where
σ<sub>i</sub> = 2u<sub>i</sub> + b<sub>i</sub>, with u<sub>i</sub> = 1 if column i holds an
upper queen and b<sub>i</sub> = 1 if row i does (Definition 9 of the paper, "Queen word"). So
U(x) = u<sub>1</sub> + … + u<sub>x</sub>: the upper bit of each symbol counts toward U.

Section 7 of the paper computes the queens with *copies* of one calculation. A copy places
queens column by column. Before placing the queen in column n it keeps a few records, among
them the least unused row m and

- the *queue* Q = σ<sub>m</sub> … σ<sub>m+|Q|−1</sub>, the symbols of σ it has read from index
  m on (nonempty; Definition 10);
- z = n − m − U(m − 1) (Definition 10), and w, R, D, A, and the upper bits of
  σ<sub>m−4</sub>, …, σ<sub>m−1</sub> (Section 7.2, equation (29)).

A copy reads σ from σ<sub>30</sub> on, one symbol at a time, and writes σ<sub>n</sub> as it
places the queen in column n; the copy that places the queens of interest (the *top*) writes
rows instead. Its *input position* p is the index of the next symbol it will read, and its
*column* n the index of the next symbol (or row) it will write. A copy is *paused* when its next
step needs a symbol it has not read yet; the paper's Algorithm 4 runs every copy until it
pauses after each symbol it reads, so after reading σ<sub>30</sub>, …, σ<sub>p−1</sub> a copy
is in a definite paused record, which we call its record *at* p.

## 2. The facts used

**F1 (a copy that reads σ follows the queens; Section 7.2).** A copy that receives the actual
symbols of σ carries out the actual calculation: its records before column n are those of the
actual board, and the symbols and rows it writes are the actual σ<sub>n</sub> and
q<sub>n</sub>. Its queue has at most 11 symbols. A single copy started at the board before
column 30 first pauses before column 48, having written σ<sub>30</sub>, …, σ<sub>47</sub>
(the table's initial output), and any symbol it then requests, σ<sub>k</sub> with k ≤ m + 6 < n,
it has already written; so it can read its own output.

**F2 (the paused records; Section 7.3).** Every record at which a copy reading σ pauses is one
of 300 *paused records*, and every step it takes (from a paused record, reading one symbol, to
the next paused record, with the symbols and rows written) is an edge of a graph on these 300
records with 476 edges. The step depends only on the record and the symbol read, so each record
has at most one edge for each symbol.

**F3 (the table; Section 7.3).** The 300 records are grouped into 82 classes, and the table
T has an entry for each class and each byte of four symbols. If a copy is at record R in class
C and reads four actual symbols s<sub>1</sub>s<sub>2</sub>s<sub>3</sub>s<sub>4</sub>, then
T[C, s<sub>1</sub>s<sub>2</sub>s<sub>3</sub>s<sub>4</sub>] holds exactly what R's four steps on
them write, and the class of the record they reach. For the top copy, each queen of an entry
is given by an upper bit and an offset, and its row is m<sub>0</sub> + offset for a lower queen
and n<sub>0</sub> + U(n<sub>0</sub> − 1) + offset for an upper one, where m<sub>0</sub> and
n<sub>0</sub> are the counters at the start of the entry (the encoding of
[`../fast_generator`](../fast_generator/), from the rows m + r and n + U(n − 1) + 1 of
Section 7.2 and Lemma 2).

**F4 (bounds on the records; Condition 15, verified in Section 6).** At every column of the
actual process, −4 ≤ z ≤ 5.

**F5 (the upper count; the proof of Lemma 20).** On the actual board before column n ≥ 30,
U(n − 1) = m + w − |D|.

**F6 (the golden ratio; Proposition 21).** For every x ≥ 0,
−3/φ < U(x) − x/φ < 2/φ.

**F7 (the forty-symbol history graph; Appendix A3, used for Corollary 19).** The paper repeats
its verification of Section 6 with histories of forty symbols instead of twelve, giving a graph
whose vertices are words of forty symbols and whose edges append a symbol and drop the oldest
([`../oeis/results/history-40.json`](../oeis/results/history-40.json), 16 876 vertices). The
actual process is a walk in it from column 80 on: every forty consecutive symbols of σ from
σ<sub>40</sub> on are a vertex, and each next symbol is the label of an edge.

**Data.** The table, the 300 records with their edges, and the class of each record are
[`../fast_generator/generated`](../fast_generator/generated/), the data of the paper's
generator; [`make_records.py`](make_records.py) turns them into `build/records.h`. The
forty-symbol graph is [`../oeis/results/history-40.json`](../oeis/results/history-40.json).

## 3. The procedure

To compute q<sub>n</sub> (`far_row` in `spire-at.c`):

0. If n < 48, the row is one of the seed's (the table's initial output).
1. If n < 32 768, run one copy from the start: the copy of F1, before column 48, reading its
   input from a prefix of σ (step B below) and walked to column n (step T).
2. Otherwise, choose the chain's positions from the top down. Let c<sub>0</sub> = n and, while
   c<sub>k</sub> ≥ 32 768,

   p<sub>k</sub> = 30 + 4⌊x<sub>k</sub>/4⌋, where x<sub>k</sub> is ⌊(c<sub>k</sub> − 560)/φ⌋
   (or one less; see below), and c<sub>k+1</sub> = p<sub>k</sub> − 128.

   Copy k will find its record at input position p<sub>k</sub> and be walked to column
   c<sub>k</sub>. Let K be the first index with c<sub>K</sub> < 32 768.
3. **(B) The bottom.** Make σ<sub>30</sub>, …, σ<sub>65 565</sub> directly, by the single copy
   of F1 reading its own output, and let "copy K" read this prefix from index c<sub>K</sub>
   on, with U(c<sub>K</sub> − 1) counted from it.
4. **(S) Starting a copy.** For k = K − 1, …, 1, then for the top (k = 0), with copy k + 1
   standing at column p<sub>k</sub> − 128 and knowing U(p<sub>k</sub> − 129):
   1. Read the next 128 symbols of copy k + 1, which are σ<sub>p−128</sub>, …,
      σ<sub>p−1</sub> (p = p<sub>k</sub>), adding their upper bits to get U(p − 1).
   2. *Find the record:* start with all 300 records as candidates; for each of the 128
      symbols, replace every candidate by its successor on that symbol, dropping candidates
      that have none. Stop with an error unless exactly one record R is left.
   3. *The counters:* m = p − |Q|, U(m − 1) = U(p − 1) − (the upper bits of the last |Q|
      symbols read), n = m + U(m − 1) + z, and U(n − 1) = m + w − |D|, with |Q|, z, w, |D|
      those of R.
   4. From R's class, run the copy on copy k + 1's next bytes (the table) up to column
      c<sub>k</sub>, adding the upper bits of the symbols it writes, to get
      U(c<sub>k</sub> − 1). **(T)** For the top, run it instead to column n, and return the
      row of the queen in column n (F3).

Only three things in this procedure involve numbers as large as n: the counters (moved by small
amounts, or compared), the positions p<sub>k</sub> (divided by φ), and the rows. `spire-at.c`
keeps them as integers of up to 64 words, and multiplies by 1/φ known to 64 × 66 bits
(computed at the start from the integer square root of 5). The product is within 2<sup>−128</sup>
of the true quotient and never above it, so x<sub>k</sub> is ⌊(c<sub>k</sub> − 560)/φ⌋ or one
less; the proofs below allow either.

## 4. Correctness

**Lemma 1 (every record has its table position).** For each of the 300 records, `records.h`
gives the table position of its class.

*Proof.* The data give each record's class. `make_records.py` follows a copy along the first
2<sup>21</sup> symbols of σ twice at once: by the record graph (F2), from the record before
column 48, and by the table (F3), from its initial position. By F3 the table position is at
every byte boundary the class of the current record, so each record met shows where its class
sits in the table. The script checks that every class is met (all 82 are) and that no class is
seen at two positions, and gives every record the position of its class. (Two compatible
classes share one position, so the table has 81 distinct positions.) ∎

**Lemma 2 (finding the record).** Let a copy reading σ be at input position p, with
p − 128 ≥ 30. If, starting from all 300 records and following the 128 symbols
σ<sub>p−128</sub>, …, σ<sub>p−1</sub> as in step S2, exactly one record is left, it is the
copy's record at p. The set left is never empty.

*Proof.* Let S<sub>j</sub> be the candidates after j symbols and R<sub>j</sub> the copy's
record at p − 128 + j. R<sub>0</sub> is a paused record of a copy reading σ, so it is one of
the 300 (F2): R<sub>0</sub> ∈ S<sub>0</sub>. If R<sub>j</sub> ∈ S<sub>j</sub>, the copy's step
from R<sub>j</sub> on σ<sub>p−128+j</sub> is an edge of the graph ending at R<sub>j+1</sub>
(F2), so R<sub>j+1</sub> ∈ S<sub>j+1</sub>. Hence R<sub>128</sub> ∈ S<sub>128</sub>, which is
therefore nonempty, and if it has one element that element is R<sub>128</sub>. ∎

The true record survives because it is consistent with the actual input; the others are
eliminated only by being inconsistent with it. Nothing is inferred from how often records occur.

**Lemma 3 (the counters).** In Lemma 2, let R have fields |Q|, z, w, D. Then at p the copy
stands before column n with least unused row m, where

  m = p − |Q|,  U(m − 1) = U(p − 1) − (u<sub>m</sub> + … + u<sub>p−1</sub>),
  n = m + U(m − 1) + z,  U(n − 1) = m + w − |D|,

and u<sub>m</sub>, …, u<sub>p−1</sub> are the upper bits of the last |Q| of the 128 symbols.

*Proof.* The queue is σ<sub>m</sub> … σ<sub>m+|Q|−1</sub> (Definition 10), and it ends with the
last symbol read, σ<sub>p−1</sub>, since every symbol read is appended to it (Algorithm 4):
so m + |Q| − 1 = p − 1. As |Q| ≤ 11 < 128 (F1), σ<sub>m</sub>, …, σ<sub>p−1</sub> are among
the 128 symbols read, which gives U(m − 1). The formula for n is the definition of z
(Definition 10), and that for U(n − 1) is F5, which applies since a paused copy stands before a
column n ≥ 48. ∎

**Lemma 4 (a started copy continues correctly).** A copy at record R at input position
p ≡ 30 (mod 4), placed at R's table position and given the actual symbols of σ from
σ<sub>p</sub> on, byte by byte, writes σ<sub>n</sub>, σ<sub>n+1</sub>, … (or, the top, the
rows q<sub>n</sub>, q<sub>n+1</sub>, …), with n as in Lemma 3.

*Proof.* The copy's input bytes start at p, so they are the bytes of the table's alignment
(four symbols from σ<sub>30</sub> on). By Lemma 1 and F3, the first entry writes what R's
four steps write, which are the actual symbols (F1, F2), and leads to the table position of the
record reached, which is the copy's record four symbols later; induction on the entries. For
the top, the rows follow from the counters of Lemma 3, advanced by each entry, and F3. ∎

**Lemma 5 (where a copy starts).** In step S, copy k's record column n<sub>R</sub> (Lemma 3)
satisfies c<sub>k</sub> − 544 < n<sub>R</sub> < c<sub>k</sub> − 507. So the copy never starts
past its column, and it walks between 508 and 543 columns to reach it.

*Proof.* Write c = c<sub>k</sub>, p = p<sub>k</sub> and y = (c − 560)/φ. Then x<sub>k</sub> >
y − 2, and 4⌊x/4⌋ ≥ x − 3 for an integer x, so y + 25 < p ≤ y + 30, and since φy = c − 560,

  c − 560 + 25φ < pφ ≤ c − 560 + 30φ, that is, c − 519.55 < pφ ≤ c − 511.46.

By Lemma 3, n<sub>R</sub> = m + U(m − 1) + z with m = p − |Q|. By F6,
U(m − 1) = (m − 1)/φ + ε with −3/φ < ε < 2/φ, and since 1 + 1/φ = φ,

  n<sub>R</sub> − pφ = −|Q|φ − 1/φ + ε + z.

With 1 ≤ |Q| ≤ 11 (F1, Definition 10) and −4 ≤ z ≤ 5 (F4), this lies between
−11φ − 4/φ − 4 > −24.28 and −φ + 1/φ + 5 = 4. Adding the two ranges gives
c − 543.83 < n<sub>R</sub> < c − 507.46. ∎

**Theorem 1 (correctness).** If `spire-at` prints a row for n, the row is q<sub>n</sub>.

*Proof.* For n < 48 the row is the seed's. For 48 ≤ n < 32 768, the single copy of F1 reads
the prefix, whose symbols are σ<sub>30</sub>, σ<sub>31</sub>, … by F1, so it writes the actual
rows. Otherwise we show, for k = K, K − 1, …, 1, that after step S copy k stands at column
c<sub>k</sub>, writes σ<sub>c<sub>k</sub></sub>, σ<sub>c<sub>k</sub>+1</sub>, …, and knows
U(c<sub>k</sub> − 1).

For k = K this is step B: the prefix is σ (F1), and U(c<sub>K</sub> − 1) is counted from it
(with U(29) from the seed). Assume it for k + 1. Since c<sub>k+1</sub> = p<sub>k</sub> − 128,
step S1 reads σ<sub>p−128</sub>, …, σ<sub>p−1</sub> and computes U(p − 1). By Lemma 2 the one
record left is copy k's record at p, by Lemma 3 its counters are right, by Lemma 4 the copy then
writes the actual symbols from column n<sub>R</sub> on, and by Lemma 5 column c<sub>k</sub> is
ahead of n<sub>R</sub>, so the walk of step S4 reaches it, with U(c<sub>k</sub> − 1) counted
from the upper bits it passes. The top copy (k = 0) is started the same way from copy 1, with
c<sub>0</sub> = n, and by Lemma 4 the row it writes in column n is q<sub>n</sub>. ∎

The choice of positions does not affect correctness: any p ≡ 30 (mod 4) with p − 128 ≥ 30
would do, as long as the copy's record column is not past c<sub>k</sub>. The positions only
decide how far each copy walks, which Lemma 5 bounds.

The same argument covers how `spire`, `spire-rows` and `spire-print` start each of their ranges
([`spire.c`](spire.c), "Starting anywhere"): the copies below the top are joined in pairs there,
and the tables of pairs and of the top are exact, since every slot is checked against its state
and a missing transition is computed from the table T.

## 5. It always prints

Lemma 2 shows that the record search never drops the true record. It remains to show that it
always drops all the others, which uses F7.

**Lemma 6 (synchronization).** Let a copy reading σ be at input position q ≥ 150. Starting
from all 300 records and following the symbols σ<sub>q</sub>, σ<sub>q+1</sub>, … as in step
S2, a single record is left after at most 58 symbols, and from then on.

*Proof.* A finite computation, [`synchronization.py`](synchronization.py) (3 seconds). At
input position 150 the copy's record is known (follow the record graph along σ from the pause
before column 48), and so are the forty symbols before it, σ<sub>110</sub> … σ<sub>149</sub>,
a vertex of the graph (F7). Call a pair (record, vertex) *reachable* if it can be reached from
this pair by following edges of the graph, each moving the record by its move on the edge's
symbol (F2); there are 16 876 reachable pairs. At every input position q ≥ 150, the copy's
record and the forty symbols before q form a reachable pair, by induction on q (F2, F7), and
the symbols σ<sub>q</sub>, σ<sub>q+1</sub>, … that follow are a path of the graph from its
vertex. The program follows every path of the graph from every reachable pair, carrying the set
of candidates that step S2 would keep (starting from all 300), and finds that on every path the
set is a single record after at most 58 symbols. A set that is a single record stays one, since
the true record always has a move (Lemma 2). ∎

(The twelve-symbol history graph of Section 6 is not enough for this: along some of its paths,
which are not pieces of σ, two records are never told apart. Nor is it enough to add the bound
of F6 on the upper queens. The forty-symbol graph excludes those paths.)

So a record search that starts at an input position of 150 or more, as step S2 does at
p − 128, leaves a single record within 58 of its 128 symbols (in every test, within 43).

**Theorem 2 (it always prints).** For every n below 2<sup>3840</sup> (about 10<sup>1156</sup>,
the limit of its integers), `spire-at` prints a row for n, and by Theorem 1 it is
q<sub>n</sub>.

*Proof.* The program stops without printing only if one of its checks fails, and none can. For
n ≥ 32 768 every record search reads from an input position p − 128 > 19 700 (below), so it
leaves exactly one record (Lemma 6); for smaller n there is no record search. No candidate set
is empty (Lemma 2); every record has a table position (Lemma 1); no copy starts past its
column, and every walk is between 508 and 543 columns (Lemma 5). Every quantity is below
2n + 2<sup>13</sup>, within the integers' 4096 bits. The chain's last copy stands at a column
c<sub>K</sub> with 19 000 < c<sub>K</sub> < 32 768 (as p<sub>K−1</sub> > 19 900, by the proof
of Lemma 5), and the copies above take fewer than 2 000 of its symbols (Section 6), so it never
reads past the prefix of 65 536 symbols. All loops are bounded by Section 6. ∎

The same holds for the ranges of `spire`, `spire-rows` and `spire-print`, whose record searches
read from input positions of 254 or more (the lowest is for a range that starts at column
65 536, whose search at 382 reads from 254).

## 6. Time and memory

Let L be the number of copies below the top, b = ⌈log<sub>2</sub> n⌉ the length of n in bits,
and consider n ≥ 32 768.

**The chain is logarithmic.** From step 2 and the bounds in the proof of Lemma 5,
c<sub>k+1</sub> = p<sub>k</sub> − 128 lies between (c<sub>k</sub> − 560)/φ − 103 and
(c<sub>k</sub> − 560)/φ − 98. So c<sub>k</sub> < n/φ<sup>k</sup>, and c<sub>k</sub> >
n/φ<sup>k</sup> − 1 200, and

  L = log<sub>φ</sub> n − log<sub>φ</sub> 32 768 + O(1) = log<sub>φ</sub> n − 21.6 + O(1).

For n = 10<sup>100</sup> this gives 457 copies, and for 10<sup>1000</sup> 4 763; the program
starts 457 and 4 764.

**Each copy does a bounded amount of work.** Let X be the number of symbols copy k writes in
all. It writes at most 543 + 11 while walking to its column (Lemma 5; a step writes at most 12
symbols), then the 128 that copy k − 1 reads to find its record, then whatever copy k − 1 reads
after that. By Lemma 3, a copy's column and input position satisfy
−24.28 < n − pφ < 4 at every pause, so while copy k − 1 writes X' symbols it reads fewer than
(X' + 28.3)/φ + 4. So X ≤ 554 + 128 + 17.5 + 4 + X'/φ. The top copy writes at most 554 rows,
and by induction down the chain every copy writes X ≤ 704 φ<sup>2</sup> < 1 850 symbols (as
704 + 704 φ<sup>2</sup>/φ = 704 φ<sup>2</sup>). Each table step writes at least 3 symbols, so a copy
takes at most 620 steps; on average it takes 261 and writes 1 690 (at 10<sup>100</sup> and
10<sup>1000</sup>, and over 2 000 random n up to 10<sup>300</sup>). Its record search follows
at most 300 candidates through 128 symbols. The top copy walks at most 543 columns.

**The numbers.** Each copy uses a fixed number of operations on numbers of b + O(1) bits:
additions and comparisons, O(b) bit operations each; one multiplication by 1/φ, O(b<sup>2</sup>)
bit operations as written (schoolbook); and additions of small numbers to its counters, O(1)
each on average (a carry past the first word is rare). The setup computes 1/φ to
b + O(1) bits, O(b<sup>2</sup>) bit operations with the bitwise square root, and σ's prefix, a
constant.

**Theorem 3 (cost).** `spire-at` computes q<sub>n</sub> in

- O(log n) time and O(log n) words of memory, counting an operation on O(log n)-bit numbers
  as one step (the usual model for numbers the size of the input);
- O(log<sup>3</sup> n) bit operations as written, O(log n · M(log n)) with a multiplication
  of cost M; and O(log<sup>2</sup> n) bits of memory, since it keeps every position
  p<sub>k</sub> (O(log n) of them would do).

*Proof.* L = O(log n) copies, each with O(1) table steps and record work and O(1) operations
on (b + O(1))-bit numbers, one of them a multiplication. A request for a symbol can pass down
the whole chain, so the recursion is at most L + 1 deep. ∎

By contrast, the generator of Section 7 (or `spire`) must make all the rows before
q<sub>n</sub>: time proportional to n (Section 7.4). Starting anywhere turns that into time
proportional to log n.

**In practice** the table steps dominate. On one core of an AMD Ryzen 7 3700X a copy takes about
20 µs (261 table steps and a record search); the multiplication by 1/φ takes a few µs even at
10<sup>1000</sup>. So the time grows in proportion to the number of digits, about 0.09 ms a
digit: 1.4 ms at 10<sup>19</sup>, 9 ms at 10<sup>100</sup>, 98 ms at 10<sup>1000</sup>. The
memory is a few megabytes (the prefix of σ, and 512 bytes for each copy's position).

## 7. Checks

`make check` runs [`synchronization.py`](synchronization.py), the computation of Lemma 6. The
proofs above also assume that `spire-at.c` carries out the procedure of Section 3, and
[`check.py`](check.py), which `make check` runs next, tests that it does:

- against the Section 7 generator's rows, at 17 columns below 10<sup>7</sup>, including the
  seed's and the edges of steps 0 and 1;
- against `spire-print` up to 10<sup>19</sup>, a separate program (tower tables and 64-bit
  numbers) that computes the rows around each column;
- against itself, with its chain aimed at three different columns (`--walk D` aims it D
  columns early, so that every copy near the top starts from a different record);
- against the bounds of Proposition 21 on q<sub>n</sub> − nφ and q<sub>n</sub> − n/φ, up to
  10<sup>1000</sup>, where any error in the large numbers would show at once.

[`make_records.py`](make_records.py) also checks the identities of Lemma 3 at 524 272 points of
σ, with the counters followed by the table.
