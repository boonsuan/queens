"""The checks behind the sharper constants (Section 6.6, "Sharper constants").

    python sharper_constants.py [history.json]

Explores the state graph exactly as verify_tuples.py does, then checks, in
exact integer arithmetic:

  1. every state satisfies  -4 <= w - |D| - phi |R| <= 1;
  2. the direct start: for 0 <= x <= 29, eps(x) = U(x) - x/phi lies strictly
     between -3/phi and 2/phi, and every lower queen in a column below 30
     has d_j - j <= 2;
  3. at every lower choice of every state, w - r - |D| <= 2, so that
     d_j - j <= 2 for every lower queen.

Together with the exact error recursion of Section 6.6, these give the
bounds of the proposition there. Comparisons with phi = (1 + sqrt 5)/2 are
made exactly, by squaring.
"""
from __future__ import annotations

import sys
from pathlib import Path

import verify_tuples
from calculation import CheckFailure, HistoryGraph
from greedy import greedy_queens

HERE = Path(__file__).resolve().parent


def less_than_phi_times(a: int, b: int) -> bool:
    """Whether a < phi * b, exactly, for integers a and b >= 0.

    2a < b + b sqrt 5  <=>  2a - b < b sqrt 5.
    """
    lhs = 2 * a - b
    if b == 0:
        return lhs < 0
    return lhs < 0 or lhs * lhs < 5 * b * b


def greater_than_phi_times(a: int, b: int) -> bool:
    """Whether a > phi * b, exactly, for integers a and b >= 0."""
    lhs = 2 * a - b
    if b == 0:
        return lhs > 0
    return lhs > 0 and lhs * lhs > 5 * b * b


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'history.json'
    graph = HistoryGraph.load(path)
    initial, successors, stats = verify_tuples.explore(graph)

    # 1. -4 <= (w - |D|) - phi|R| <= 1 for every state.
    lowest = highest = None
    for s in successors:
        a, b = s.w - len(s.D), len(s.R)
        # a - phi b >= -4  <=>  not (a + 4 < phi b)
        if less_than_phi_times(a + 4, b):
            raise CheckFailure(f'w - |D| - phi|R| < -4 at {s}')
        # a - phi b <= 1  <=>  not (a - 1 > phi b)
        if greater_than_phi_times(a - 1, b):
            raise CheckFailure(f'w - |D| - phi|R| > 1 at {s}')
        value = a - b * (1 + 5 ** 0.5) / 2          # for the report only
        lowest = value if lowest is None else min(lowest, value)
        highest = value if highest is None else max(highest, value)

    # 2. The direct start, columns 0..29.
    q = greedy_queens(30)
    U = 0
    j = 0
    worst_discrepancy = None
    for x, y in enumerate(q):
        if x >= 1 and y > x:
            U += 1
        if x >= 1 and y < x:
            j += 1
            dj = x - y
            worst_discrepancy = dj - j if worst_discrepancy is None else max(worst_discrepancy, dj - j)
            if dj - j > 2:
                raise CheckFailure(f'd_j - j > 2 for the lower queen in column {x}')
        # eps(x) < 2/phi  <=>  phi U < x + 2 ;  eps(x) > -3/phi  <=>  phi U > x - 3
        if not greater_than_phi_times(x + 2, U):     # need x + 2 > phi U
            raise CheckFailure(f'eps({x}) >= 2/phi')
        if not less_than_phi_times(x - 3, U):        # need x - 3 < phi U
            raise CheckFailure(f'eps({x}) <= -3/phi')

    # 3. From column 30 on, d_j - j = w - r - |D| <= 2 at every lower choice.
    if stats.largest_discrepancy > 2:
        raise CheckFailure('w - r - |D| > 2 at some lower choice')

    print('VERIFIED')
    print('states checked:', len(successors))
    print(f'range of w - |D| - phi|R| over the states: [{lowest:.4f}, {highest:.4f}] '
          '(within [-4, 1])')
    print('start: -3/phi < eps(x) < 2/phi for 0 <= x <= 29; '
          f'largest d_j - j before column 30: {worst_discrepancy}')


if __name__ == '__main__':
    main()
