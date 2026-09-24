"""A finite consistency check of Section 5.2 against 3000 directly computed queens.

    python check_correspondence.py

For every column n from 30 through 2999, run the branch of the calculation
that reads the actual earlier symbols, and check that it

  * finds every requested symbol on an edge of the history graph,
  * requests only symbols with index at most m + 6 < n,
  * chooses the actual queen q_n and produces the actual symbol sigma_n, and
  * gives exactly the records of the actual board before column n + 1.

This tests the implementation on a long finite stretch; the statement for
all columns is the induction of Section 6.4.
"""
from __future__ import annotations

from pathlib import Path

from actual_branch import follow
from calculation import CheckFailure, HistoryGraph

HERE = Path(__file__).resolve().parent
LAST = 2999


def main() -> None:
    graph = HistoryGraph.load(HERE / 'history.json')
    steps = 0
    largest_offset = -1          # largest requested index minus m
    smallest_margin = LAST       # smallest n minus requested index
    for step in follow(graph, 30, LAST):
        steps += 1
        for index, _, _ in step.requests:
            if index > step.board.m + 6 or index >= step.board.n:
                raise CheckFailure(f'column {step.board.n} requested sigma_{index}')
            largest_offset = max(largest_offset, index - step.board.m)
            smallest_margin = min(smallest_margin, step.board.n - index)
    print('CONSISTENT')
    print('columns checked:', f'30 through {LAST} ({steps} steps)')
    print('largest requested offset from m:', largest_offset)
    print('smallest distance from a requested index to n:', smallest_margin)


if __name__ == '__main__':
    main()
