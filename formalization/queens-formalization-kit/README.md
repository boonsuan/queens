# Formalizing "Greedy Queens and the Golden Ratio" in Lean 4 and mathlib

This kit contains everything needed to formalize the paper
*Greedy Queens and the Golden Ratio* by Boon Suan Ho: the LaTeX source,
the compiled PDF, and the companion code that carries out the paper's
finite computation. The goal is a Lean 4 + mathlib project that proves
the paper's main theorem, with every result on the way stated as
closely as practical to the paper.

Snapshot of 2026-09-25: paper at manuscript commit `fde88f8`, companion
code at `fda31e8` (github.com/boonsuan/queens). The paper goes to arXiv
tonight; small wording edits may still follow, but the mathematics is
settled.

## What is in the kit

| Path | Contents |
|---|---|
| `paper/queens.pdf` | The paper as compiled. Result numbers below refer to it. |
| `paper/queens.tex` | Master file; it inputs everything else in `paper/`. |
| `paper/sections/` | One file per section, in order (see the map below). |
| `paper/preamble.tex`, `frontmatter.tex`, `references.tex`, `figures/` | Macros, title and abstract, bibliography, TikZ figures. |
| `companion/` | The companion repository: `verification/` (Sections 4–6), `oeis/` (Section 6.5), `fast_generator/` (Section 7). Each folder has a README. |

The paper compiles with `latexmk -pdf queens.tex` (pdfLaTeX with
`-shell-escape` for the TikZ figures), but the PDF is already here.

## The theorem

Place a queen in each column $n = 0, 1, 2, \dots$ of a quarter-infinite
board, in the lowest row $q_n$ not attacked along a row, diagonal or
antidiagonal by an earlier queen (OEIS A275895). Theorem 1: for every
$n \ge 1$, with $\phi = (1+\sqrt5)/2$,

- $|q_n - n\phi| < 5/\phi$ if $q_n > n$ (upper queens), and
- $|q_n - n/\phi| < 4 + 5/\phi$ if $q_n < n$ (lower queens).

## How the proof is organized

| Section | File | Results |
|---|---|---|
| 1 Introduction | `01-introduction.tex` | Theorem 1 (`thm:main`) |
| 2 Upper queens and rows | `02-upper-queens-and-rows.tex` | Lemma 2 (upper queens), Lemma 3 ($q$ is a permutation of $\mathbb N$), Lemma 4 (sorted lower rows: $v_j = j + U(j-1)$) |
| 3 Diagonal discrepancy to the golden ratio | `03-golden-ratio.tex` | Lemma 5 ($\lvert d_j - j\rvert \le 4$), Lemma 6, Lemma 7, Proposition 8; the deduction of Theorem 1 from Lemma 5 |
| 4 The local rule | `04-local-rule.tex` | Definitions 9–11 (queen word, local state, history graph), Propositions 12–13, Definition 14 (state graph) |
| 5 Sufficient records | `05-sufficient-records.tex` | Condition 15, Lemma 16 (the records determine the actual step) |
| 6 Finite verification | `06-finite-verification.tex` | Proposition 17 (the finite check), the induction proving Lemma 5 (§6.4), Corollaries 18–19, Lemma 20, Proposition 21 (sharper constants) |
| 7 Fast generation | `07-fast-generation.tex` | Proposition 22; an algorithm, not needed for Theorem 1 |
| Appendix A | `appendix-a-reproduction.tex` | How the computations are run and reproduced |

The logical spine is:

1. **Sections 2–3 (pure mathematics).** Lemma 5, the bounded diagonal
   discrepancy, implies Theorem 1 through Lemmas 4, 6, 7 and the
   contraction of Proposition 8. This part is conventional real and
   integer analysis and is a good place to start: prove Theorem 1 with
   Lemma 5 as a hypothesis.
2. **Sections 4–5 (the local description).** The greedy step at column
   $n$ is determined by a finite *local state*: records $w, z, R, D, A$
   and three words $H_{\mathrm{in}}, Q, H_{\mathrm{out}}$ over the
   alphabet $\{0,1,2,3\}$. Lemma 16 says that under Condition 15 the
   calculation on the local state reproduces the actual greedy step.
3. **Section 6 (the finite computation and the induction).**
   Proposition 17 is a finite check: from the starting state before
   column 30, every branch of the calculation, with requests answered
   by a fixed history graph, stays within Condition 15. The
   induction of §6.4 then follows the actual queens forever and yields
   Lemma 5. The first 30 columns are checked directly.

## The finite computation

Proposition 17 is the computational core, and the Python code in
`companion/verification/` is its reference implementation:

- `calculation.py`: the calculation on a local state (Algorithm 1 of
  the paper), with the history graph and the Condition 15 check.
- `construct_history_graph.py`: how the history graph was built
  (Algorithm 2). The proof only needs the finished graph.
- `verify_tuples.py`: the exhaustive check of Proposition 17
  (Algorithm 3). It reports 7014 states and 8327 state-graph edges.
- `verify_bitmasks.py`, `compare_verifiers.py`: an independent second
  implementation and the comparison between the two.
- `history.json`: the history graph, `{"memory": 12, "vertices": [[code, mask], ...]}`.
  Each vertex is a word of 12 symbols from $\{0,1,2,3\}$ (symbol
  $= 2u + b$, column bit $u$, row bit $b$), encoded as a 12-digit
  base-4 number, oldest symbol first. `mask` has bit $s$ set when the
  vertex has an outgoing edge labelled $s$; following that edge drops
  the oldest symbol and appends $s$. There are 2092 vertices and 2603
  edges, and the graph is closed.
- `greedy.py`, `trace.py`, `actual_branch.py`: the greedy queens
  themselves and the actual local states column by column, useful for
  testing a Lean implementation against Python.

The quick check is `python companion/verification/verify_tuples.py`
(a few seconds, Python 3.10+, no dependencies).

How to carry this computation into Lean is a design decision for the
formalization: for example a Lean implementation of the check proved
by `decide` or by kernel reduction, or `native_decide`, which trusts
the compiler. Whichever is chosen, document it, and report
`#print axioms` for the main theorem.

## What to deliver

- A Lake project (`lean-toolchain` pinned, mathlib as a dependency)
  that builds with `lake build` and contains no `sorry`.
- A statement of Theorem 1 that a reader can compare with the paper
  directly: $q$ defined from the greedy rule as simply as possible,
  and the bounds with $\phi = (1+\sqrt5)/2$ from mathlib's
  `goldenRatio`.
- A README mapping each Lean declaration to the paper result it
  formalizes (by name and number), and listing the axioms used.
- Priorities: Theorem 1 first, via Lemma 5. After that, if time
  allows, Lemma 3, Corollaries 18–19 and Proposition 21. Section 7 is
  out of scope.

If the paper and the code ever disagree, or a step in the paper is
unclear or wrong, note it rather than working around it silently; the
author wants to know.
