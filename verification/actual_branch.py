"""The branch of the calculation that reads the actual earlier symbols.

Section 5.2 of the paper concerns this branch: on an actual board, when every
request is answered with the actual earlier symbol of the queen word, the
calculation carries out the actual greedy step. This module runs that branch
column after column and checks it against the board computed directly by
greedy.py. It is used by check_correspondence.py and trace.py.
"""
from __future__ import annotations

from typing import Iterator, NamedTuple

from calculation import Calculation, CheckFailure, HistoryGraph, State
from greedy import Board, greedy_queens, local_state, queen_word


class ActualBranch(Calculation):
    """The calculation with every request answered by the actual symbol."""

    def __init__(self, graph: HistoryGraph, state: State, board: Board, sigma: list):
        super().__init__(graph, state)
        self.board = board
        self.sigma = sigma
        self.requests: list[tuple[int, int, tuple]] = []  # (index, symbol, symbols allowed)
        self.choice: int | None = None

    def answers(self, Q: tuple) -> tuple:
        index = self.board.m + len(Q)
        allowed = super().answers(Q)
        symbol = self.sigma[index]
        if symbol not in allowed:
            raise CheckFailure(f'sigma_{index} = {symbol} does not label an edge')
        self.requests.append((index, symbol, allowed))
        return (symbol,)

    def choose_queen(self, Q: tuple, r: int):
        for choice in super().choose_queen(Q, r):
            if r == 0:                          # the outermost call makes the choice
                self.choice = choice[0]
            yield choice


class Step(NamedTuple):
    """One column of the actual process."""
    board: Board             # m, d, U(m-1) before column n
    state: State             # the stored records before column n
    choice: int | None       # the lower offset r, or None for an upper queen
    row: int                 # q_n
    symbol: int              # sigma_n
    requests: list           # (index, symbol, symbols allowed by the graph)
    successor: State         # the records before column n+1
    next_board: Board


def follow(graph: HistoryGraph, first: int, last: int) -> Iterator[Step]:
    """Run the actual branch for columns first, ..., last, starting from the
    board before column 30, and check every step against the direct board.

    The queue of each state is whatever the requests so far have made it, so
    the direct board is computed with the same queue length.
    """
    q = greedy_queens(last + 2)
    sigma = queen_word(q)
    state, board = local_state(q, 30, memory=graph.memory)
    for n in range(30, last + 1):
        expected, board = local_state(q, n, memory=graph.memory, queue_length=len(state.Q))
        if state != expected:
            raise CheckFailure(f'the records before column {n} differ from the board')
        branch = ActualBranch(graph, state, board, sigma)
        successors = list(branch.successors())
        if len(successors) != 1:
            raise CheckFailure(f'the actual branch gave {len(successors)} successors at column {n}')
        successor = successors[0]
        # A lower choice r means row m + r; an upper choice means a row above n.
        if branch.choice is None:
            chose_actual_queen = q[n] > n
        else:
            chose_actual_queen = q[n] == board.m + branch.choice
        if not chose_actual_queen:
            raise CheckFailure(f'the queen chosen in column {n} is not q_{n} = {q[n]}')
        if successor.H_out[-1] != sigma[n]:
            raise CheckFailure(f'the symbol produced in column {n} is not sigma_{n}')
        if n >= first:
            _, next_board = local_state(q, n + 1, memory=graph.memory,
                                        queue_length=len(successor.Q))
            yield Step(board, state, branch.choice, q[n], sigma[n],
                       branch.requests, successor, next_board)
        state = successor
    expected, _ = local_state(q, last + 1, memory=graph.memory, queue_length=len(state.Q))
    if state != expected:
        raise CheckFailure(f'the records before column {last + 1} differ from the board')
