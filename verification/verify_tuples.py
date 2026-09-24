"""The exhaustive check of Section 6.3, using the calculation of Section 4.5.

    python verify_tuples.py [history.json]

Checks, with the history graph held fixed and no edges added:

  1. the graph is well formed (every edge ends at a vertex);
  2. the starting board (Section 6.1): the word sigma_1 ... sigma_29 follows
     the graph, every lower queen before column 30 satisfies |d_j - j| <= 4,
     and the state before column 30 satisfies the bounds of Section 5 with
     U(m-1) >= 12;
  3. from every state reached, every branch of the calculation passes the
     output check and gives a successor satisfying the bounds of Section 5.

Any failure stops the program with an error; no branch is ever dropped to
make the check pass. The states reached form the state graph of Section 4.5.
"""
from __future__ import annotations

import sys
from collections import deque
from pathlib import Path

from calculation import (Calculation, CheckFailure, HistoryGraph, State, Statistics,
                         encode, satisfies_condition)
from greedy import greedy_queens, local_state, queen_word

HERE = Path(__file__).resolve().parent


def starting_state(graph: HistoryGraph, start: int = 30) -> State:
    """Check the starting board and return the state before column `start`."""
    L = graph.memory
    q = greedy_queens(start)
    sigma = queen_word(q)
    # sigma_1 ... sigma_{start-1} follows the graph: every window is a vertex,
    # and each next symbol labels an edge leaving the window before it.
    for t in range(L, start):
        window = tuple(sigma[t - L + 1:t + 1])
        if window not in graph.edges:
            raise CheckFailure(f'the window ending at index {t} is not a vertex')
        if t + 1 < start and sigma[t + 1] not in graph.edges[window]:
            raise CheckFailure(f'sigma_{t + 1} does not label an edge')
    # The diagonal discrepancy of every lower queen before the start.
    j = 0
    for x, y in enumerate(q):
        if y < x:
            j += 1
            if abs((x - y) - j) > 4:
                raise CheckFailure(f'|d_j - j| > 4 for the lower queen in column {x}')
    state, board = local_state(q, start, memory=L)
    if board.kappa < 12:
        raise CheckFailure('U(m-1) >= 12 fails at the start')
    if not satisfies_condition(state):
        raise CheckFailure(f'the starting state {state} violates the bounds')
    return state


def explore(graph: HistoryGraph, start: int = 30):
    """Explore the state graph from the state before column `start`.

    Returns (initial state, map from each state to its set of successors,
    statistics). A state already examined is not examined again: its
    branches depend only on its eight fields and the fixed graph.
    """
    initial = starting_state(graph, start)
    stats = Statistics()
    successors: dict[State, frozenset] = {}
    pending = deque([initial])
    seen = {initial}
    while pending:
        state = pending.popleft()
        found = set()
        for successor in Calculation(graph, state, stats).successors():
            if not satisfies_condition(successor):
                raise CheckFailure(f'a successor of {state} violates the bounds: {successor}')
            found.add(successor)
        successors[state] = frozenset(found)
        for t in successors[state]:
            if t not in seen:
                seen.add(t)
                pending.append(t)
    return initial, successors, stats


def canonical(s: State) -> tuple:
    """An encoding shared with verify_bitmasks.py, for compare_verifiers.py."""
    mask = lambda offsets: sum(1 << a for a in offsets)
    return (s.w, s.z, mask(s.R), mask(s.D), mask(s.A),
            encode(s.H_in), len(s.Q), encode(s.Q), encode(s.H_out))


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'history.json'
    graph = HistoryGraph.load(path)
    initial, successors, stats = explore(graph)
    print('VERIFIED')
    print('history-graph vertices and edges:', graph.vertex_count(), graph.edge_count())
    print('state-graph vertices and edges:', len(successors),
          sum(map(len, successors.values())))
    print('completed choices:', stats.choices)
    print('completed lower choices:', stats.lower_choices)
    print('largest fresh input offset:', stats.largest_fresh_offset)
    print('largest row advance:', stats.largest_row_advance)
    print('range of w-r-|D| at lower choices:',
          [stats.smallest_discrepancy, stats.largest_discrepancy])
    print('requests with no outgoing edge:', stats.stopped_branches)


if __name__ == '__main__':
    main()
