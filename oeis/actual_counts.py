"""How much of the history graph and the state graph the actual queens use.

    python actual_counts.py

The twelve-symbol history graph (2092 vertices, 2603 edges) and state graph
(7014 states, 8327 edges) allow more than the board produces. This program
finds exactly which of their vertices, edges, states, and edges between states
are actual: windows sigma_{i-11} ... sigma_i of the queen word (i >= 12), edges
between consecutive windows, states before columns n >= 30 (Section 6.4), and
transitions S_n -> S_{n+1}. Result: 1824 windows, 2195 history-graph edges,
4749 states, and 5207 transitions; every one occurs before column 1600000.

Each count is shown exact by a lower and an upper bound that agree.

  * Lower bound: the ones that occur in the first 1600000 columns, by running
    the greedy queens and the branch that reads the actual symbols.
  * Upper bound: from column 80 on, the queen word follows the forty-symbol
    history graph, and the actual forty-symbol states are states of the
    forty-symbol state graph (graphs.py, Appendix A3). Keeping the last twelve
    symbols of each history maps forty-symbol windows and states to twelve-
    symbol ones. The forty-symbol state before column 80 holds the whole queue
    from m to sigma_79, while the actual twelve-symbol state, run from column
    30, may hold a shorter one; the two actual branches are run side by side
    until their states agree after this map, and from then on they agree in
    every column, since they read the same symbols. So every actual twelve-
    symbol state from that column on is the image of a forty-symbol state
    reachable from the one there, and the earlier ones are added directly.
    Windows and edges ending before index 80 are likewise added directly.
"""
from __future__ import annotations

import graphs
from graphs import State, local_state, require

from actual_branch import ActualBranch      # noqa: E402  (from ../verification)
from greedy import Board                    # noqa: E402
from states import queens                   # noqa: E402

COLUMNS = 1_600_000
MEMORY = 12


def last12(s: State) -> State:
    return s._replace(H_in=s.H_in[-MEMORY:], H_out=s.H_out[-MEMORY:])


def run() -> list[str]:
    twelve = graphs.twelve_symbol_graph()
    forty = graphs.forty_symbol_graph()

    # The actual queens and queen word: sigma_i = 2 u_i + b_i.
    q, m_at, d_at, upper = queens(COLUMNS + 2)
    size = len(q)
    upper_row = bytearray(size)
    for x in range(1, size):
        if x < q[x] < size:
            upper_row[q[x]] = 1
    sigma = [None] + [2 * (q[i] > i) + upper_row[i] for i in range(1, size)]

    def step(graph, state, n):
        board = Board(n, m_at[n], d_at[n], upper[m_at[n]])
        (successor,) = list(ActualBranch(graph, state, board, sigma).successors())
        return successor

    # Lower bounds: what occurs before column COLUMNS.
    windows, edges = set(), set()
    for i in range(MEMORY, COLUMNS):
        window = tuple(sigma[i - MEMORY + 1:i + 1])
        windows.add(window)
        if i + 1 < COLUMNS:
            edges.add((window, sigma[i + 1]))
    early_states = {}                       # the actual state before each column 30 .. 199
    state = local_state(q, 30, memory=MEMORY)[0]
    states, transitions = {state}, set()
    for n in range(30, COLUMNS):
        if n < 200:
            early_states[n] = state
        successor = step(twelve.history, state, n)
        states.add(successor)
        transitions.add((state, successor))
        state = successor

    # Upper bounds from the forty-symbol graphs.
    up_windows = {v[-MEMORY:] for v in forty.history.edges}
    up_edges = {(v[-MEMORY:], s) for v, labels in forty.history.edges.items() for s in labels}
    up_windows |= {tuple(sigma[i - MEMORY + 1:i + 1]) for i in range(MEMORY, 80)}
    up_edges |= {(tuple(sigma[i - MEMORY + 1:i + 1]), sigma[i + 1]) for i in range(MEMORY, 80)}

    number = {s: k for k, s in enumerate(forty.states)}
    state40 = local_state(q, 80, memory=40)[0]
    require(number.get(state40) == 0, 'the forty-symbol state before column 80 is not the initial state')
    agree = 80
    while last12(state40) != early_states[agree]:
        state40 = step(forty.history, state40, agree)
        agree += 1
    reached, todo = {number[state40]}, [number[state40]]
    while todo:
        for t, _ in forty.out[todo.pop()]:
            if t not in reached:
                reached.add(t)
                todo.append(t)
    up_states = {last12(forty.states[k]) for k in reached}
    up_transitions = {(last12(forty.states[k]), last12(forty.states[t])) for k in reached for t, _ in forty.out[k]}
    for n in range(30, agree):
        up_states.add(early_states[n])
        up_transitions.add((early_states[n], early_states[n + 1]))

    lines = []
    for name, found, bound, total in [
            ('windows (history-graph vertices)', windows, up_windows, twelve.history.vertex_count()),
            ('history-graph edges', edges, up_edges, twelve.history.edge_count()),
            ('states', states, up_states, len(twelve.states)),
            ('state-graph edges', transitions, up_transitions, twelve.edge_count())]:
        require(found == bound, f'{name}: {len(found)} occur, but the upper bound is {len(bound)}')
        lines.append(f'{name}: exactly {len(found)} of {total} are actual')
    lines.append(f'(the actual branches with histories 12 and 40 agree from column {agree} on)')
    return lines


def main() -> None:
    try:
        lines = run()
    except graphs.CheckFailure as failure:
        raise SystemExit(f'FAIL: {failure}')
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
