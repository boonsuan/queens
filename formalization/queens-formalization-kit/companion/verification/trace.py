"""Print the actual local states and steps, column by column.

    python trace.py [first [last]]        (default: columns 41 through 44)

For each column n, prints the absolute values n, m, d, U(m-1) (used only to
interpret the records), the eight stored records, the requests the
calculation makes and the symbols the history graph allows for them, the
queen chosen, the new symbol sigma_n, and the advances mu and nu of the row
and diagonal references. Every step is checked against the board computed
directly from the greedy rule. Section 4.6 of the paper works through
columns 41, 42, 47, and 53 by hand; this program reproduces those numbers.
"""
from __future__ import annotations

import sys
from pathlib import Path

from actual_branch import follow
from calculation import HistoryGraph

HERE = Path(__file__).resolve().parent


def word(symbols) -> str:
    return ''.join(map(str, symbols))


def offsets(values) -> str:
    return '{' + ','.join(map(str, sorted(values))) + '}' if values else '{}'


def main() -> None:
    if len(sys.argv) == 1:
        first, last = 41, 44
    else:
        first = int(sys.argv[1])
        last = int(sys.argv[2]) if len(sys.argv) > 2 else first
    if first < 30:
        raise SystemExit('the local calculation starts at column 30')
    graph = HistoryGraph.load(HERE / 'history.json')
    for step in follow(graph, first, last):
        b, s = step.board, step.state
        print(f'before column {b.n}:  m = {b.m}, d = {b.d}, U(m-1) = {b.kappa}')
        print(f'  w = {s.w}, z = {s.z}, R = {offsets(s.R)}, D = {offsets(s.D)}, A = {offsets(s.A)}')
        print(f'  H_in = {word(s.H_in)}   Q = {word(s.Q)}   H_out = {word(s.H_out)}')
        for index, symbol, allowed in step.requests:
            print(f'  request sigma_{index}: graph allows {list(allowed)}, actual {symbol}')
        kind = f'lower, offset r = {step.choice}' if step.choice is not None else 'upper'
        mu = step.next_board.m - b.m
        nu = step.next_board.d - b.d
        print(f'  queen ({b.n}, {step.row}), {kind};  sigma_{b.n} = {step.symbol};'
              f'  mu = {mu}, nu = {nu}')
        print()
    t = step.successor
    print(f'before column {last + 1}:')
    print(f'  w = {t.w}, z = {t.z}, R = {offsets(t.R)}, D = {offsets(t.D)}, A = {offsets(t.A)}')
    print(f'  H_in = {word(t.H_in)}   Q = {word(t.Q)}   H_out = {word(t.H_out)}')


if __name__ == '__main__':
    main()
