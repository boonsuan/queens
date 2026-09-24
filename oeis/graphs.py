"""The two state graphs and the graphs derived from them (Section 6.5, Appendix A).

    python graphs.py

Every program in this directory starts from one of two state graphs:

  * the twelve-symbol state graph of the finite verification of Section 6.3: the history graph
    ../verification/history.json, explored from the state before column 30;
  * the forty-symbol state graph: the same calculation with histories of
    length 40, explored from the state before column 80. Its history graph is
    built by the construction of Section 6.2 with length 40 and start column
    80, and saved as results/history-40.json.

Each graph is explored with its history graph held fixed, by verify_tuples.py
of ../verification: every branch is followed, and a missing output edge or a
successor violating the bounds of Section 5 is an error. So loading a saved graph file
is safe: it is checked in full every time it is used.

The actual greedy process is a single walk in each state graph, starting at
the initial state; the output symbol of the edge S -> S' taken before column
n+1 is sigma_n, the last symbol of S'.H_out. Its upper-column bit
u_n = [q_n > n] is sigma_n >> 1. Two graphs are derived from a state graph
by contracting paths, as in Appendix A:

  * the gap graph, whose walk spells the gaps between upper columns
    (A275888) from the first upper column at or after column 79 on;
  * the run graph, whose walk spells the lengths of the maximal runs of
    lower columns (A275885).

Running this file rebuilds results/history-40.json (about 30 seconds) and
prints the sizes of both state graphs. The other programs build that file
themselves when it is missing.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parent / 'verification'
RESULTS = HERE / 'results'
# The calculation and the exhaustive check are those of ../verification.
sys.path.insert(0, str(VERIFICATION))

from calculation import CheckFailure, HistoryGraph, State, Statistics, upper  # noqa: E402
from construct_history_graph import construct                                 # noqa: E402
from greedy import greedy_queens, local_state                                 # noqa: E402
from verify_tuples import explore                                             # noqa: E402

FORTY_SYMBOL_HISTORY = RESULTS / 'history-40.json'


def require(condition: bool, message: str) -> None:
    """Stop with an error unless the condition holds. (Unlike assert, this
    check cannot be switched off by running Python with -O.)"""
    if not condition:
        raise CheckFailure(message)


# ------------------------------------------------------------ state graphs

@dataclass
class StateGraph:
    """A state graph with its states numbered; the initial state is 0.

    out[v] lists the edges leaving state v as pairs (t, symbol), where t is
    the successor and symbol its output symbol, the last symbol of H_out.
    """
    memory: int
    start: int
    history: HistoryGraph
    states: list[State]
    out: list[list[tuple[int, int]]]
    statistics: Statistics

    def edge_count(self) -> int:
        return sum(map(len, self.out))


def explore_state_graph(history: HistoryGraph, start: int) -> StateGraph:
    """Run the exhaustive check of Section 6.3 and number the states reached."""
    initial, successors, statistics = explore(history, start)
    states = [initial] + [s for s in successors if s != initial]
    number = {s: i for i, s in enumerate(states)}
    out = [sorted((number[t], t.H_out[-1]) for t in successors[s]) for s in states]
    require(statistics.stopped_branches == 0, 'a request found no outgoing edge')
    return StateGraph(history.memory, start, history, states, out, statistics)


@lru_cache(maxsize=None)
def twelve_symbol_graph() -> StateGraph:
    """The state graph of the finite verification of Section 6.3 (history length 12, start column 30)."""
    history = HistoryGraph.load(VERIFICATION / 'history.json')
    graph = explore_state_graph(history, 30)
    require((history.vertex_count(), history.edge_count()) == (2092, 2603),
            'the twelve-symbol history graph does not have 2092 vertices and 2603 edges')
    require((len(graph.states), graph.edge_count()) == (7014, 8327),
            'the twelve-symbol state graph does not have 7014 states and 8327 edges')
    return graph


def build_forty_symbol_history() -> HistoryGraph:
    """Construct the forty-symbol history graph (Section 6.2 with length 40,
    start column 80) and save it as results/history-40.json."""
    history = construct(memory=40, start=80)['graph']
    RESULTS.mkdir(exist_ok=True)
    history.save(FORTY_SYMBOL_HISTORY)
    return history


def check_start_before_column_80() -> dict:
    """The starting records of the forty-symbol verification (Appendix A).

    Computed directly from the first 80 queens: m = 51, d = 32, U(m-1) = 31,
    w = -3, z = -2, R = D = A = empty. The input history, queue, and output
    history hold sigma_11..sigma_50, sigma_51..sigma_79, sigma_40..sigma_79,
    so every stored index is positive and below 80. The hypothesis of
    the lemma of Section 5 is U(m-1) >= 12 (not 40), and it holds.
    """
    state, board = local_state(greedy_queens(80), 80, memory=40)
    records = {'m': board.m, 'd': board.d, 'U(m-1)': board.kappa, 'w': state.w, 'z': state.z,
               'R': sorted(state.R), 'D': sorted(state.D), 'A': sorted(state.A),
               'input history': [board.m - 40, board.m - 1],
               'queue': [board.m, board.m + len(state.Q) - 1],
               'output history': [80 - 40, 79]}
    expected = {'m': 51, 'd': 32, 'U(m-1)': 31, 'w': -3, 'z': -2, 'R': [], 'D': [], 'A': [],
                'input history': [11, 50], 'queue': [51, 79], 'output history': [40, 79]}
    require(records == expected, f'unexpected records before column 80: {records}')
    return records


@lru_cache(maxsize=None)
def forty_symbol_graph() -> StateGraph:
    """The forty-symbol state graph (history length 40, start column 80)."""
    if not FORTY_SYMBOL_HISTORY.exists():
        build_forty_symbol_history()
    history = HistoryGraph.load(FORTY_SYMBOL_HISTORY)
    check_start_before_column_80()
    graph = explore_state_graph(history, 80)
    require((history.vertex_count(), history.edge_count()) == (16876, 17499),
            'the forty-symbol history graph does not have 16876 vertices and 17499 edges')
    require((len(graph.states), graph.edge_count()) == (29267, 30000),
            'the forty-symbol state graph does not have 29267 states and 30000 edges')
    return graph


# ------------------------------------------------------------ derived graphs

def gap_graph(graph: StateGraph) -> dict[int, set[tuple[int, int]]]:
    """The gap graph: contract each path from one upper output to the next.

    Its vertices are the states whose last output symbol is upper, that is,
    the states immediately after an upper column. From such a state v, follow
    lower outputs until the next upper output, reaching t after k steps; this
    gives an edge v --k--> t. On the actual walk, k is the gap from one upper
    column to the next. Four lower outputs in a row would mean four
    consecutive lower columns, which the history graph excludes; meeting
    them is therefore an error, so every label is 1, 2, 3, or 4.
    """
    vertices = [v for v, s in enumerate(graph.states) if upper(s.H_out[-1])]
    edges: dict[int, set[tuple[int, int]]] = {v: set() for v in vertices}
    for v in vertices:
        paths = [(v, 0)]            # (state reached, lower outputs so far)
        while paths:
            u, lower = paths.pop()
            for t, symbol in graph.out[u]:
                if upper(symbol):
                    edges[v].add((t, lower + 1))
                else:
                    require(lower + 1 < 4, f'four lower outputs in a row from state {v}')
                    paths.append((t, lower + 1))
    return edges


def run_graph(gaps: dict[int, set[tuple[int, int]]]) -> dict[int, set[tuple[int, int]]]:
    """The run graph: delete the unit gaps and relabel each other gap k by k - 1.

    A gap k > 1 between upper columns encloses a lower run of length k - 1,
    and a unit gap encloses none. So from each gap-graph vertex v, follow
    unit-gap edges to some u, then take one edge u --k--> t with k > 1; this
    gives an edge v --(k-1)--> t. On the actual walk, the labels are the
    successive terms of A275885. Five unit gaps in a row would mean six
    consecutive upper columns, which the history graph excludes; meeting
    them is an error.
    """
    edges: dict[int, set[tuple[int, int]]] = {v: set() for v in gaps}
    for v in gaps:
        paths = [(v, 0)]            # (vertex reached, unit gaps so far)
        while paths:
            u, units = paths.pop()
            for t, k in gaps[u]:
                if k > 1:
                    edges[v].add((t, k - 1))
                else:
                    require(units + 1 < 5, f'five unit gaps in a row from vertex {v}')
                    paths.append((t, units + 1))
    return edges


def topological_order(vertices: set[int], successors) -> list[int] | None:
    """The vertices in an order where every edge goes forward (Kahn's
    algorithm), or None if the edges successors(v) inside `vertices` form a
    cycle."""
    indegree = dict.fromkeys(vertices, 0)
    for v in vertices:
        for t in successors(v):
            if t in indegree:
                indegree[t] += 1
    ready = [v for v in vertices if indegree[v] == 0]
    order = []
    while ready:
        v = ready.pop()
        order.append(v)
        for t in successors(v):
            if t in indegree:
                indegree[t] -= 1
                if indegree[t] == 0:
                    ready.append(t)
    return order if len(order) == len(vertices) else None


def describe(graph: StateGraph) -> str:
    return (f'{graph.memory}-symbol history graph: {graph.history.vertex_count()} vertices, '
            f'{graph.history.edge_count()} edges; state graph from column {graph.start}: '
            f'{len(graph.states)} states, {graph.edge_count()} edges')


def run() -> list[str]:
    build_forty_symbol_history()
    records = check_start_before_column_80()
    lines = [describe(twelve_symbol_graph()), describe(forty_symbol_graph())]
    s = forty_symbol_graph().statistics
    lines.append(f'40-symbol check: {s.choices} choices, {s.lower_choices} lower, '
                 f'largest fresh offset {s.largest_fresh_offset}, largest row advance '
                 f'{s.largest_row_advance}, w-r-|D| in [{s.smallest_discrepancy}, '
                 f'{s.largest_discrepancy}], no request without an edge')
    lines.append('records before column 80: ' + ', '.join(f'{k} = {v}' for k, v in records.items()))
    return lines


def main() -> None:
    for line in run():
        print(line)
    print('written:', FORTY_SYMBOL_HISTORY)


if __name__ == '__main__':
    main()
