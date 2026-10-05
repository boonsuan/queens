"""Print the actual local state before column n, quickly, for any n >= 30.

    python states.py n [n ...]           for example:  python states.py 30-39 100 1000000

For each column n, prints the eight stored records of a local state
(w, z, R, D, A, H_in, Q, H_out; Section 4.2), together with m, d, and
U(m-1). Table 5 of the paper (Section 7.5) lists the states before columns
30-39 and 10^2, ..., 10^6.

How it is fast. The queens are computed in linear time: in column n the
greedy rule tries only the lower candidates m, ..., n - d (Section 4.1), and
otherwise places the queen on the next upper diagonal, at row n + U(n)
(Lemma 3). The records w, z, R, D, A, H_in, and H_out are read off this
board (greedy.local_state). The queue Q is different: it holds the symbols
the calculation has read so far from index m on, so its length depends on
the calculation's past. The calculation reads only near the least unused
row (every request ends by index m + 6, by Lemma 17), so the queue before
column n depends only on the last stretch of columns. The program starts the actual branch a short window before n,
with a queue of one symbol, and runs it up to column n. It then checks the
result twice: the records must agree with the board, and a run started from
a window twice as long must reach the same state, queue included.
"""
from __future__ import annotations

import sys
from array import array
from pathlib import Path

from actual_branch import ActualBranch
from calculation import CheckFailure, HistoryGraph, State
from greedy import Board, greedy_queens, local_state, queen_word

HERE = Path(__file__).resolve().parent
WINDOW = 40          # columns; the run starts where m is at least this far behind


def queens(count: int):
    """q_0, ..., q_{count-1}, with m, d, and the upper counts, in linear time.

    Returns (q, m, d, upper), where m[n] and d[n] are the least unused row and
    lower-diagonal magnitude before column n, and upper[c] is the number of
    upper queens in the columns less than c.
    """
    q = array('q', [0])
    m_at, d_at, upper = array('q', [0, 1]), array('q', [0, 1]), array('q', [0, 0])
    size = 3 * count + 3
    row_used, diag_used, anti_used = bytearray(size), bytearray(size), bytearray(size)
    row_used[0] = anti_used[0] = 1
    diag_used[0] = 1                       # lower-diagonal magnitude n - y = 0 holds the origin
    m, d, U = 1, 1, 0
    for n in range(1, count):
        y = -1
        for candidate in range(m, n - d + 1):          # the lower candidates, Section 4.1
            if not (row_used[candidate] or diag_used[n - candidate] or anti_used[n + candidate]):
                y = candidate
                break
        if y < 0:
            U += 1
            y = n + U                                    # the next upper queen (Section 2)
        else:
            diag_used[n - y] = 1
        q.append(y)
        row_used[y] = 1
        anti_used[n + y] = 1
        while row_used[m]:
            m += 1
        while diag_used[d]:
            d += 1
        m_at.append(m)
        d_at.append(d)
        upper.append(U)
    return q, m_at, d_at, upper


def run(graph, q, sigma, m_at, d_at, upper, start: int, n: int) -> State:
    """The actual branch from column `start` to column n.

    From column 30 it starts with the state of Section 6.1, whose queue runs
    up to sigma_29; from a later column, with a queue of one symbol.
    """
    queue = None if start == 30 else 1
    state, _ = local_state(q, start, memory=graph.memory, queue_length=queue)
    for k in range(start, n):
        board = Board(k, m_at[k], d_at[k], upper[m_at[k]])
        successors = list(ActualBranch(graph, state, board, sigma).successors())
        if len(successors) != 1:
            raise CheckFailure(f'the actual branch gave {len(successors)} successors at column {k}')
        state = successors[0]
    return state


def state_before(graph, q, sigma, m_at, d_at, upper, n: int) -> State:
    def start_behind(gap: int) -> int:
        k = n
        while k > 30 and m_at[k] > m_at[n] - gap:
            k -= 1
        return k
    near = run(graph, q, sigma, m_at, d_at, upper, start_behind(WINDOW), n)
    far = run(graph, q, sigma, m_at, d_at, upper, start_behind(2 * WINDOW), n)
    if near != far:
        raise CheckFailure(f'the state before column {n} depends on where the run starts')
    direct, _ = local_state(q, n, memory=graph.memory, queue_length=len(near.Q))
    if direct != near:
        raise CheckFailure(f'the records before column {n} differ from the board')
    return near


def parse(args: list[str]) -> list[int]:
    columns = []
    for a in args:
        first, _, last = a.partition('-')
        columns += range(int(first), int(last or first) + 1)
    if not columns or min(columns) < 30:
        raise SystemExit('give columns n >= 30, such as: python states.py 30-39 100 1000000')
    return columns


def main() -> None:
    columns = parse(sys.argv[1:])
    graph = HistoryGraph.load(HERE / 'history.json')
    q, m_at, d_at, upper = queens(max(columns) + 2)
    check = greedy_queens(min(len(q), 3000))
    if list(q[:len(check)]) != check:
        raise CheckFailure('the fast queens differ from the greedy rule')
    sigma = queen_word(q)
    word = lambda symbols: ''.join(map(str, symbols))
    offsets = lambda values: '{' + ','.join(map(str, sorted(values))) + '}' if values else '{}'
    for n in columns:
        s = state_before(graph, q, sigma, m_at, d_at, upper, n)
        print(f'before column {n}:  m = {m_at[n]}, d = {d_at[n]}, U(m-1) = {upper[m_at[n]]}')
        print(f'  w = {s.w}, z = {s.z}, R = {offsets(s.R)}, D = {offsets(s.D)}, A = {offsets(s.A)}')
        print(f'  H_in = {word(s.H_in)}   Q = {word(s.Q)}   H_out = {word(s.H_out)}')


if __name__ == '__main__':
    main()
