"""The local state, the history graph, and the calculation (Sections 4.2-4.5).

Given a local state before column n and a fixed history graph, the
calculation (Section 4.5 and Algorithm 1 of the paper) chooses the queen in column n,
produces the new queen-word symbol sigma_n, and updates the eight records
for column n+1. It uses only the stored records and the graph, so it can be
run on any state, whether or not the state comes from an actual board.

Whenever the calculation needs the symbol just after the end of the queue Q,
it makes a *request*. The possible answers are the labels of the edges
leaving the vertex formed by the last symbols of H_in Q (Section 4.3). With
several edges the calculation splits into *branches*, one per edge; with
none, the current branch stops. The calculation returns the successor state
of every branch that does not stop.

Notation, as in the paper:
    state    (w, z, R, D, A, H_in, Q, H_out)                 Section 4.2
    symbol   2u + b, with upper-column bit u and upper-row bit b
    offset   h for column (or row) m + h, where m is the least unused row
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, NamedTuple


class State(NamedTuple):
    """A local state (Section 4.2).

    R, D, A are sets of offsets; H_in, Q, H_out are tuples of symbols, oldest
    first. On a board before column n, with least unused row m and least
    unused lower-diagonal magnitude d:
        w = n - m - d            width of the lower candidate interval
        z = n - m - U(m-1)       locates column n among the upper queens
        R, D, A                  lower-queen rows, magnitudes and antidiagonals,
                                 measured from m, d and n + m
        H_in = sigma_{m-L} ... sigma_{m-1}      (L = history length)
        Q    = sigma_m ... sigma_{m+|Q|-1}
        H_out = sigma_{n-L} ... sigma_{n-1}
    """
    w: int
    z: int
    R: frozenset
    D: frozenset
    A: frozenset
    H_in: tuple
    Q: tuple
    H_out: tuple


def upper(symbol: int) -> int:
    """The upper-column bit u of a symbol 2u + b."""
    return symbol >> 1


def row_bit(symbol: int) -> int:
    """The upper-row bit b of a symbol 2u + b."""
    return symbol & 1


def satisfies_condition(s: State) -> bool:
    """The bounds of Section 5.1: w <= 4, -4 <= z <= 5, and R, D contained in [1..4]."""
    return (s.w <= 4 and -4 <= s.z <= 5
            and all(1 <= a <= 4 for a in s.R)
            and all(1 <= a <= 4 for a in s.D))


class CheckFailure(Exception):
    """A check of Section 6.3 failed; the verification stops."""


# --------------------------------------------------------------- history graph

def encode(word: tuple) -> int:
    """A word as a base-four number, with the newest symbol as the last digit."""
    code = 0
    for symbol in word:
        code = 4 * code + symbol
    return code


def decode(code: int, length: int) -> tuple:
    """The inverse of encode for words of the given length."""
    return tuple((code >> 2 * (length - 1 - i)) & 3 for i in range(length))


class HistoryGraph:
    """The history graph (Section 4.3).

    Its vertices are words of length `memory`. An edge W --s--> W' says that
    the symbol s may follow W; its destination W' is W with s appended and the
    oldest symbol dropped. The graph is stored as a map from each vertex to
    the set of symbols labeling its outgoing edges.

    File format (history.json): {"memory": L, "vertices": [[h, mask], ...]},
    where h encodes a vertex as above and bit s of mask is set when an edge
    labeled s leaves it.
    """

    def __init__(self, memory: int, edges: dict[tuple, set]):
        self.memory = memory
        self.edges = edges

    @classmethod
    def load(cls, path: Path) -> HistoryGraph:
        """Read a graph and check that it is well formed: each vertex is
        listed once and every edge ends at a listed vertex."""
        data = json.loads(Path(path).read_text())
        memory = data['memory']
        edges: dict[tuple, set] = {}
        for code, mask in data['vertices']:
            if not (0 <= code < 4 ** memory and 0 <= mask < 16):
                raise CheckFailure(f'invalid vertex record {[code, mask]}')
            word = decode(code, memory)
            if word in edges:
                raise CheckFailure(f'vertex {word} is listed twice')
            edges[word] = {s for s in range(4) if mask >> s & 1}
        graph = cls(memory, edges)
        for word, symbols in edges.items():
            for s in symbols:
                if graph.destination(word, s) not in edges:
                    raise CheckFailure(f'the edge {word} --{s}--> leaves the vertex list')
        return graph

    def save(self, path: Path) -> None:
        records = sorted([encode(w), sum(1 << s for s in symbols)]
                         for w, symbols in self.edges.items())
        data = {'memory': self.memory, 'vertices': records}
        Path(path).write_text(json.dumps(data, separators=(',', ':')) + '\n', newline='\n')

    def destination(self, word: tuple, symbol: int) -> tuple:
        return word[1:] + (symbol,)

    def symbols_after(self, word: tuple) -> tuple:
        """The labels of the edges leaving a vertex, in increasing order."""
        if word not in self.edges:
            raise CheckFailure(f'{word} is not a vertex of the history graph')
        return tuple(sorted(self.edges[word]))

    def vertex_count(self) -> int:
        return len(self.edges)

    def edge_count(self) -> int:
        return sum(len(symbols) for symbols in self.edges.values())


# ----------------------------------------------------------------- calculation

@dataclass
class Statistics:
    """Counts reported by the verification (Appendix A)."""
    choices: int = 0                # completed queen choices, over all branches
    lower_choices: int = 0
    stopped_branches: int = 0       # requests at a vertex with no outgoing edge
    largest_fresh_offset: int = -1  # largest offset of a requested symbol
    largest_row_advance: int = 0    # largest mu
    smallest_discrepancy: int = 0   # range of w - r - |D| at lower choices
    largest_discrepancy: int = 0


class Calculation:
    """The calculation of Section 4.5 applied to one state, with the fixed history graph.

    Algorithm 1 in the paper describes a single branch, in which Extend(k)
    may split the calculation. Here Extend and the two loops of Algorithm 1
    (choosing the queen and searching for a free row) are generators that
    yield once per branch, so successors() carries out every branch. A queue
    is a tuple, so appending a symbol in one branch never changes the queue
    of another.
    """

    def __init__(self, graph: HistoryGraph, state: State,
                 statistics: Statistics | None = None):
        self.graph = graph
        self.s = state
        self.stats = statistics if statistics is not None else Statistics()

    # ------------------------------------------------------------ requests

    def answers(self, Q: tuple) -> tuple:
        """Answer a request: the symbols that may follow H_in Q (Section 4.3)."""
        vertex = (self.s.H_in + Q)[-self.graph.memory:]
        return self.graph.symbols_after(vertex)

    def extend_queue(self, Q: tuple, k: int) -> Iterator[tuple]:
        """Extend(k) of Algorithm 1, in every branch: yield each queue reached
        from Q by requests until |Q| >= k.

        A branch whose request finds no outgoing edge stops and yields nothing.
        """
        if len(Q) >= k:
            yield Q
            return
        symbols = self.answers(Q)
        if not symbols:
            self.stats.stopped_branches += 1
            return
        self.stats.largest_fresh_offset = max(self.stats.largest_fresh_offset, len(Q))
        for symbol in symbols:
            yield from self.extend_queue(Q + (symbol,), k)

    # ------------------------------------------------ upper queens (Section 4.4)

    def upper_columns(self, Q: tuple) -> list[tuple[int, int]]:
        """The pairs (h, Gamma(h)) for the upper columns m + h stored in H_in and Q.

        Gamma(h) = U(m+h) - U(m-1), computed from the stored upper-column
        bits (Section 4.4): for h >= 0 it counts upper columns m, ..., m+h; for
        h < 0 it is minus the number of upper columns m+h+1, ..., m-1.
        """
        columns = []
        count = 0
        for h in range(-1, -len(self.s.H_in) - 1, -1):
            if upper(self.s.H_in[h]):
                columns.append((h, -count))
            count += upper(self.s.H_in[h])
        count = 0
        for h, symbol in enumerate(Q):
            count += upper(symbol)
            if upper(symbol):
                columns.append((h, count))
        return columns

    def antidiagonal_attack(self, Q: tuple, r: int) -> bool:
        """The antidiagonal criterion of Section 4.4: an upper queen in column m + h attacks the candidate
        (n, m + r) along its antidiagonal exactly when 2h + Gamma(h) = z + r."""
        return any(2 * h + gamma == self.s.z + r for h, gamma in self.upper_columns(Q))

    def adjustment(self, Q: tuple, x: int) -> int:
        """The adjustment J(x) of Section 4.4: the upper queens in Q with relative row h + Gamma(h) <= x,
        minus those in H_in with relative row > x."""
        value = 0
        for h, gamma in self.upper_columns(Q):
            if h >= 0 and h + gamma <= x:
                value += 1
            elif h < 0 and h + gamma > x:
                value -= 1
        return value

    # ------------------------------------------------ the four stages (Section 4.5)

    def choose_queen(self, Q: tuple, r: int) -> Iterator[tuple[int | None, tuple]]:
        """The loop of Algorithm 1 that chooses the queen, from candidate r on,
        in every branch: yield (r, T) for the first candidate that passes all
        five tests, or (None, T) for an upper queen.

        T is the branch's queue after the requests made while testing. The loop
        is written recursively, so that after a request splits the calculation,
        each branch goes on to the next candidate with its own queue.
        """
        s = self.s
        if r > s.w:
            yield None, Q
            return
        if r in s.R or s.w - r in s.D or r in s.A:     # attacked by a lower queen
            yield from self.choose_queen(Q, r + 1)
            return
        # The row bit is at offset r; an antidiagonal attacker in Q has h <= (z+r)/2.
        k = 1 + max(r, (s.z + r) // 2)
        for T in self.extend_queue(Q, k):
            if row_bit(T[r]) == 0 and not self.antidiagonal_attack(T, r):
                yield r, T
            else:
                yield from self.choose_queen(T, r + 1)

    def output_check(self, symbol: int) -> tuple:
        """Check that the new symbol labels an edge leaving H_out (Section 4.3),
        and return the new output history, the destination of that edge."""
        if symbol not in self.graph.symbols_after(self.s.H_out):
            raise CheckFailure(f'no output edge for symbol {symbol} from H_out {self.s.H_out}')
        return self.graph.destination(self.s.H_out, symbol)

    def find_free_row(self, Q: tuple, h: int, R_tilde: frozenset) -> Iterator[tuple[int, tuple]]:
        """The row search of Algorithm 1, from offset h on, in every branch:
        yield (mu, T), where mu is the first offset >= h whose row holds neither
        a recorded lower queen nor an upper queen, and T is the branch's queue."""
        for T in self.extend_queue(Q, h + 1):
            if h not in R_tilde and row_bit(T[h]) == 0:
                yield h, T
            else:
                yield from self.find_free_row(T, h + 1, R_tilde)

    def successors(self) -> Iterator[State]:
        """The calculation of Section 4.5: the successor state of every branch that does not stop."""
        s = self.s
        memory = self.graph.memory
        # Prepare the symbols needed for J(z-1) and J(z).
        for T in self.extend_queue(s.Q, s.z):
            for r, V in self.choose_queen(T, 0):
                self.stats.choices += 1
                lower = r is not None
                # Produce and check the new symbol (the row count of Section 4.4).
                b_out = self.adjustment(V, s.z) - self.adjustment(V, s.z - 1)
                symbol = 2 * int(not lower) + b_out
                H_out = self.output_check(symbol)
                # Record a lower queen, then find the new references.
                R_t, D_t, A_t = s.R, s.D, s.A
                if lower:
                    self.stats.lower_choices += 1
                    discrepancy = s.w - r - len(s.D)            # d_j - j (Section 4.1)
                    self.stats.smallest_discrepancy = min(self.stats.smallest_discrepancy, discrepancy)
                    self.stats.largest_discrepancy = max(self.stats.largest_discrepancy, discrepancy)
                    R_t, D_t, A_t = R_t | {r}, D_t | {s.w - r}, A_t | {r}
                nu = next(h for h in range(len(D_t) + 1) if h not in D_t)
                for mu, W in self.find_free_row(V, 0, R_t):
                    self.stats.largest_row_advance = max(self.stats.largest_row_advance, mu)
                    P, Q_new = W[:mu], W[mu:]
                    yield State(                     # the record update of Section 4.5
                        w=s.w + 1 - mu - nu,
                        z=s.z + 1 - mu - sum(upper(a) for a in P),
                        R=frozenset(a - mu for a in R_t if a >= mu),
                        D=frozenset(a - nu for a in D_t if a >= nu),
                        A=frozenset(a - 1 - mu for a in A_t if a >= 1 + mu),
                        H_in=(s.H_in + P)[-memory:],
                        Q=Q_new,
                        H_out=H_out)
