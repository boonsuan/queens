# Related OEIS questions

This is a sequence-by-sequence assessment of the OEIS entries about the
greedy queens board: what the paper proves about them, what the witnesses
in this directory show to be attained, and what remains open. It
distinguishes three kinds of statement.

* **Proved:** a universal statement about all terms, from the main theorem
  or from a finite graph derived from the verification (an upper bound; see
  [`README.md`](README.md)).
* **Attained:** an occurrence in the actual sequence, found in a computed
  prefix (a witness).
* **Open:** a question or observation that neither settles.

It covers 26 entries that describe the same board, its coordinates, its
orderings, and its runs, gaps, and counts: A065185, A065188, A065189,
A199134, A275884–A275902, A276324, A276325, and A276783. It also covers the
full game array A269526/A274528, of which the queens are the positions of
the value 1 (value 0 in the zero-based version), with its rows, columns,
diagonals, and statistics. Other queen problems, such as Wythoff variants,
spiral boards, queen-plus-knight rules, and optimal packings of finite
boards, concern different processes and are not included.

Notation follows the paper: q_n is the row of the queen in column n
(zero-based), U(n) and L(n) count the upper and lower queens in columns
1, ..., n, phi is the golden ratio, and p(N) = q_(N-1) + 1 is the one-based
permutation A065188. As in the OEIS, the origin counts as an upper column
in the upper-column sequences. The question catalogue for A275888 is the
note [*Observations about A275888*](https://oeis.org/A275888/a275888.txt)
by Boon Suan Ho, linked from that entry.

## 1. Runs and gaps of upper and lower columns

These are the entries settled in Section 6.5 of the paper.

### A275885: lengths of runs of lower columns

The entry conjectures that all terms are 1, 2, or 3, and asks whether a 4
occurs.

* **Proved:** every term is at most 3; four consecutive lower columns never
  occur (twelve-symbol history graph).
* **Attained:** 1, 2, and 3, first at indices 3, 1, and 1390.
* The set of values is exactly {1, 2, 3}, which settles the conjecture.
  This is the same fact as the bound 4 for A275888.

### A275886: lengths of runs of upper columns

The entry states no conjecture.

* **Proved:** every term is at most 5; six consecutive upper columns never
  occur (twelve-symbol history graph).
* **Attained:** 1, ..., 5, first at indices 3, 9, 1, 2, and 13.
* The set of values is exactly {1, ..., 5}.

### A275887: run lengths of equal terms in A275885

The entry records the first occurrences of 1 through 9 and of 11 in the
terms examined; 10 does not appear. It does not state a conjecture about
all terms.

* **Proved:** every term lies in {1, ..., 9, 11}. In the forty-symbol run
  graph, the lengths of maximal runs of c's are L_1 = {1, ..., 9, 11},
  L_2 = {1, ..., 6}, and L_3 = {1}; the initial runs, through column 95,
  are checked directly. In particular, 10 and every value above 11 never
  occur.
* **Attained:** every value, and every length in each L_c. The first
  indices agree with those recorded in the entry:

  | Value | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 11 |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
  | First index | 7 | 1 | 29 | 14 | 4 | 22 | 64 | 178 | 534 | 230 |

* The set of values is exactly {1, ..., 9, 11}, the range the entry
  records. The twelve-symbol graph permits a maximal run of ten 1s, so the
  exclusion of 10 needs the forty-symbol graph. Both boundaries of a run
  matter: a run of eleven 1s contains ten consecutive 1s, which do not form
  a maximal run.

### A275888: gaps between upper columns

The entry conjectures that every term is at most 4. The linked note lists
156 return words to 3, of which 63 appear faithful, and records
observations about the 4s.

* **Proved** (twelve-symbol graph): every term is at most 4, and the
  factors 11111, 2222, 33, 44, and 3213 never occur. So 213 is not a
  return word to 3.
* **Proved** (forty-symbol graph): every return word to 3 is one of the
  156 words of the note; their lengths range from 2 to 26, and exactly five
  contain a 4. Each of 63 words has only one possible successor, so these
  63 are faithful. Consecutive 4s are at least 71 terms apart, and every
  pair at distance 71 has the fill given in the note.
* **Attained:** the value 4, first at index 3073 (upper columns 4969 and
  4973). All 156 return words, the last by index 108015. Two different
  successors for each of the other 93 words, the last pair by index 573517,
  so exactly 63 words are faithful. The distance 71, at indices 83418 and
  83489.
* The set of values is exactly {1, 2, 3, 4}, which settles the conjecture.
* **Open:** the proposed maximum distance 24853 between consecutive 4s;
  the numbers of fills at longer distances, such as three at distance 877
  and four at distance 8362; the mean distance between 4s, near 3336; and
  limiting frequencies of words. The forty-symbol gap graph contains a
  cycle avoiding 4 that can be entered after a 4 and left toward a 4, so it
  gives no upper bound for the distance between consecutive 4s. The cycle
  is not known to occur in the actual sequence; the obstruction is in the
  graph only. A proof would need a finer abstraction, obtained by the same
  unrestricted construction and check, not by deleting unwanted paths.

### A275889: gaps between lower columns

The entry states no conjecture.

* **Proved:** every term is at most 6, since a gap between lower columns is
  one more than the upper run it encloses.
* **Attained:** 1, ..., 6, first at indices 1, 4, 12, 13, 2, and 17.
* The set of values is exactly {1, ..., 6}. The mean gap is phi^2
  (Section 2 below).

## 2. Consequences of the main results

These follow from the paper's main estimates without further computation.
The entries state the limits below only where noted; they are consequences,
not resolved conjectures.

The counting entries are

* A275890(N) = 1 + U(N-1), the number of i <= N with p(i) >= i;
* A275891(N) = L(N-1), the number of i <= N with p(i) < i;
* A275892(N) = 1 + U(N-1) - L(N-1), their difference.

The bound |U(n) - n/phi| < 5/phi gives N/phi + O(1), N/phi^2 + O(1), and
N/phi^3 + O(1) respectively.

Writing t_j for the jth upper column and x_j^L for the jth lower column,
|t_j - phi j| < 5 and |x_j^L - phi^2 j| < 5 phi. So the enumerations of
upper columns (A275884, and A275894 in zero-based form) and of lower
columns (A199134, and A275893 in zero-based form) have slopes phi and
phi^2 with bounded error, and the mean gaps in A275888 and A275889 are phi
and phi^2. The limit of the proportion of upper queens stated in A275884
follows from the main theorem.

By the diagonal-coverage corollary, the signed diagonal sequences A065185
(p(N) - N) and A276325 (the same diagonals in antidiagonal visitation
order) each enumerate the integers exactly once. For the full array this
is the case of the value 1 (value 0 in A274528) of the expectation that
every value occurs on every infinite diagonal; the other values remain
open.

A further consequence, not stated in the paper: the number H(S) of queens
with x + y <= S satisfies H(S) = 2S/phi^3 + O(1). Each upper queen has
coordinate sum 2 t_j + j = phi^3 j + O(1); each lower queen has
x_j^L = phi^2 j + O(1) and y_j^L = phi j + O(1), since |d_j - j| <= 4, so
the same sum estimate holds; and no two queens share an antidiagonal. So
A276324 and A276783 (the occupied antidiagonals, in increasing order) have
slope phi^3/2 with bounded error.

## 3. Inventory of the 26 entries

| Entry | Relation to the board | Status |
|---|---|---|
| [A065185](https://oeis.org/A065185) | p(N) - N, the signed diagonal | Proved: enumerates the integers exactly once |
| [A065188](https://oeis.org/A065188) | The one-based permutation p | Main theorem: bounded distance from the lines of slopes phi and 1/phi |
| [A065189](https://oeis.org/A065189) | Inverse of A065188 | A permutation by row coverage; no further question |
| [A199134](https://oeis.org/A199134) | Columns with p(N) < N | Proved: slope phi^2, bounded error |
| [A275884](https://oeis.org/A275884) | Columns with p(N) >= N, with the origin | Proved: slope phi; the stated ratio limit follows from the main theorem |
| [A275885](https://oeis.org/A275885) | Lengths of runs of lower columns | Proved and attained: exactly {1, 2, 3}; conjecture settled |
| [A275886](https://oeis.org/A275886) | Lengths of runs of upper columns | Proved and attained: exactly {1, ..., 5} |
| [A275887](https://oeis.org/A275887) | Run lengths of equal terms in A275885 | Proved and attained: exactly {1, ..., 9, 11} |
| [A275888](https://oeis.org/A275888) | Gaps between upper columns | Proved and attained: exactly {1, 2, 3, 4}; return words, faithful words, minimum 4-distance settled; maximum 4-distance open |
| [A275889](https://oeis.org/A275889) | Gaps between lower columns | Proved and attained: exactly {1, ..., 6}; mean phi^2 |
| [A275890](https://oeis.org/A275890) | Number of i <= N with p(i) >= i | N/phi + O(1) |
| [A275891](https://oeis.org/A275891) | Number of i <= N with p(i) < i | N/phi^2 + O(1) |
| [A275892](https://oeis.org/A275892) | Difference of the two counts | N/phi^3 + O(1) |
| [A275893](https://oeis.org/A275893) | Lower columns, zero-based | As A199134; no further question |
| [A275894](https://oeis.org/A275894) | Upper columns, zero-based | As A275884; no further question |
| [A275895](https://oeis.org/A275895) | q_n, the paper's sequence | Main theorem: bounded distance from the lines of slopes phi and 1/phi |
| [A275896](https://oeis.org/A275896) | Inverse of q, zero-based | A permutation by row coverage; no further question |
| [A275897](https://oeis.org/A275897) | Visitation indices of the queens, zero-based | Reindexing; no further question |
| [A275898](https://oeis.org/A275898) | The same, one-based | Reindexing; no further question |
| [A275899](https://oeis.org/A275899) | One-based x coordinates in antidiagonal order | A permutation, since each column has one queen |
| [A275900](https://oeis.org/A275900) | One-based y coordinates in antidiagonal order | A permutation by row coverage |
| [A275901](https://oeis.org/A275901) | Zero-based x coordinates in that order | As A275899; no further question |
| [A275902](https://oeis.org/A275902) | Zero-based y coordinates in that order | As A275900; no further question |
| [A276324](https://oeis.org/A276324) | Occupied antidiagonals in increasing order | Slope phi^3/2 (Section 2); no further question |
| [A276325](https://oeis.org/A276325) | Signed diagonals in visitation order | Proved: enumerates the integers exactly once |
| [A276783](https://oeis.org/A276783) | Occupied coordinate sums, zero-based | A shift of A276324 |

## 4. The full game array

The queens are the positions of one value of the game array, so the
results above say little about the other values.

| Entry | Question | Status |
|---|---|---|
| [A269526](https://oeis.org/A269526), [A274528](https://oeis.org/A274528) | The full array, one-based and zero-based: every infinite diagonal expected to be a permutation; periodicity of differences in fixed columns | Rows and columns are permutations (proved in A269526). For diagonals, only the value 1 (0) is settled here. Periodicity would need records of all game values; open |
| [A274318](https://oeis.org/A274318) | The main diagonal, conjectured to be a permutation | Open; the unique 1 on it is not enough |
| [A274315](https://oeis.org/A274315) | The first row; a formula or recurrence is requested | A permutation, as for every row of A269526; a formula is open |
| [A274316](https://oeis.org/A274316), [A274317](https://oeis.org/A274317), [A274791](https://oeis.org/A274791) | Other fixed rows | Permutations, as for every row; no further question |
| [A295563](https://oeis.org/A295563) | First zero-based row; asks for a formula and about apparent slopes near 0.48 and 1.29 | Open; these are values along a row, not positions of zeros |
| [A295564](https://oeis.org/A295564), [A295565](https://oeis.org/A295565) | Coordinates of the lower branch of A295563; A295565 asks whether the ratio converges | Open |
| [A295566](https://oeis.org/A295566), [A295567](https://oeis.org/A295567) | Coordinates of the upper branch; A295567 asks the same question | Open |
| [A274614](https://oeis.org/A274614), [A274615](https://oeis.org/A274615) | The third column; A274615 proposes an affine formula of period 16 | Open; a plausible target for a separate finite check (see Section 5) |
| [A274617](https://oeis.org/A274617), [A274619](https://oeis.org/A274619) | The fourth column, one-based and zero-based | No question on these entries |
| [A273138](https://oeis.org/A273138), [A273139](https://oeis.org/A273139) | First appearances of values, and record positions | The bound a(n) <= 6 in A273138 is stated only for n <= 80 (a(81) = 10); no universal claim |
| [A274529](https://oeis.org/A274529), [A275883](https://oeis.org/A275883) | Distinct values and maxima on antidiagonals | No question; they involve every value |
| [A274530](https://oeis.org/A274530), [A274652](https://oeis.org/A274652) | Antidiagonal sums | No question |
| [A274534](https://oeis.org/A274534) | Counts of each value through successive antidiagonals | Its first column counts the queens and satisfies the estimate for H(S) of Section 2; nothing is claimed about the other columns |
| [A274616](https://oeis.org/A274616) | Maximum number of nonattacking queens on triangular boards | A different optimization problem |

## 5. Notes on the entries

The FORMULA line of A065188 relates it to A275895 with the wrong sign. With
the data and definitions of both entries, the correct identity is

    A065188(N) = A275895(N-1) + 1,

as the first terms already show.

The formula proposed in A274615 gives a(0) = 0, whereas the data of the
entry begin with 1. This needs to be resolved before the formula can be
stated for all terms.

For the upper/lower orientation of the counting entries, use the
inequalities p(N) >= N and p(N) < N: the geometric descriptions in the
entries can differ in orientation.
