"""The greedy queens and their local records, computed from the definition.

Everything here comes straight from the greedy rule that defines q_n: the
rows q_0, q_1, ..., the queen word sigma (Section 4.2), and the eight
records of the local state before a given column (Section 4.2). Nothing
here uses the local calculation, so these functions can be used to check
that calculation against the actual board.
"""
from __future__ import annotations

from typing import NamedTuple

from calculation import State


def greedy_queens(count: int) -> list[int]:
    """Return q_0, ..., q_{count-1}.

    In each column n, the queen goes in the lowest row y that shares no row,
    diagonal (y - n), or antidiagonal (y + n) with an earlier queen.
    """
    rows, diagonals, antidiagonals = set(), set(), set()
    q = []
    for n in range(count):
        y = 0
        while y in rows or y - n in diagonals or y + n in antidiagonals:
            y += 1
        q.append(y)
        rows.add(y)
        diagonals.add(y - n)
        antidiagonals.add(y + n)
    return q


def queen_word(q: list[int]) -> list:
    """Return [None, sigma_1, ..., sigma_{len(q)-1}], the queen word of Section 4.2.

    sigma_i = 2 u_i + b_i, where u_i = 1 if column i has an upper queen and
    b_i = 1 if row i has one. An upper queen in row i lies in a column below
    i, so these symbols are determined by the columns 0, ..., len(q)-1.
    Index 0 is unused, so that sigma[i] is sigma_i.
    """
    upper_rows = {y for x, y in enumerate(q) if y > x}
    return [None] + [2 * int(q[i] > i) + int(i in upper_rows) for i in range(1, len(q))]


class Board(NamedTuple):
    """Absolute values before column n. The local state does not store them;
    they are used only to explain and check the records."""
    n: int
    m: int      # least unused row
    d: int      # least unused lower-diagonal magnitude
    kappa: int  # U(m-1): the number of upper queens in columns below m


def local_state(q: list[int], n: int, memory: int = 12,
                queue_length: int | None = None) -> tuple[State, Board]:
    """The local state before column n of the board q_0, ..., q_{n-1}.

    The queue holds sigma_m, ..., sigma_{m+queue_length-1}; by default it runs
    up to sigma_{n-1}. The histories H_in and H_out have `memory` symbols.
    """
    queens = q[:n]
    sigma = queen_word(queens)
    lower = [(x, y) for x, y in enumerate(queens) if y < x]
    used_rows = set(queens)
    m = next(y for y in range(n + 1) if y not in used_rows)
    magnitudes = {x - y for x, y in lower}
    d = next(e for e in range(1, n + 1) if e not in magnitudes)
    kappa = sum(1 for c in range(1, m) if queens[c] > c)
    if m <= memory:
        raise ValueError(f'the input history before column {n} would need nonpositive indices')
    end = n if queue_length is None else m + queue_length
    state = State(
        w=n - m - d,
        z=n - m - kappa,
        R=frozenset(y - m for x, y in lower if y >= m),
        D=frozenset(x - y - d for x, y in lower if x - y >= d),
        A=frozenset(x + y - (n + m) for x, y in lower if x + y >= n + m),
        H_in=tuple(sigma[m - memory:m]),
        Q=tuple(sigma[m:end]),
        H_out=tuple(sigma[n - memory:n]),
    )
    return state, Board(n, m, d, kappa)
