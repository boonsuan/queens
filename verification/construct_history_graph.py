"""Construct the history graph by running the calculation (Section 6.2).

    python construct_history_graph.py [--memory L] [--start N] [--output FILE]

Start with the windows of length L of the directly computed word
sigma_1 ... sigma_{N-1} and the edges between consecutive windows. Then run
the calculation on every state reached from the state before column N, with
one difference: when a computed symbol fails the output check, its edge (and
the destination vertex) is added to the graph instead of causing an error. A
successor violating the bounds of Section 5.1 is still an error. An added
edge is a new answer to later requests, so the exploration is repeated until
a complete pass adds no edge.

The result is the smallest graph that contains the starting windows and has
an edge for every output it permits, so it does not depend on the order of
exploration. The proof does not rely on this construction: verify_tuples.py
and verify_bitmasks.py check the finished graph with no edges added.

With the defaults (L = 12, N = 30) the result is history.json. A longer
history needs a later start, so that the input history before column N has
positive indices; the OEIS checks use L = 40 and N = 80.
"""
from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path

import verify_tuples
from calculation import Calculation, CheckFailure, HistoryGraph, satisfies_condition
from greedy import greedy_queens, queen_word

HERE = Path(__file__).resolve().parent


class GrowingCalculation(Calculation):
    """The calculation, but a failed output check adds the missing edge."""

    def output_check(self, symbol: int) -> tuple:
        H_out = self.s.H_out
        destination = self.graph.destination(H_out, symbol)
        self.graph.edges[H_out].add(symbol)
        self.graph.edges.setdefault(destination, set())
        return destination


def starting_graph(memory: int, start: int) -> HistoryGraph:
    """The windows of sigma_1 ... sigma_{start-1} and their consecutive edges."""
    sigma = queen_word(greedy_queens(start))
    edges: dict[tuple, set] = {}
    for t in range(memory, start):
        window = tuple(sigma[t - memory + 1:t + 1])
        edges.setdefault(window, set())
        if t + 1 < start:
            edges[window].add(sigma[t + 1])
    return HistoryGraph(memory, edges)


def construct(memory: int = 12, start: int = 30, state_limit: int = 2_000_000) -> dict:
    """Build the graph; return it with a report of every exploration."""
    graph = starting_graph(memory, start)
    report = {'memory': memory, 'start_column': start,
              'starting_vertices': graph.vertex_count(),
              'starting_edges': graph.edge_count(), 'explorations': []}
    initial = verify_tuples.starting_state(graph, start)
    states = {initial}
    while True:
        edges_before = graph.edge_count()
        # Each pass examines every state known so far, in a fixed order.
        pending = deque(sorted(states, key=verify_tuples.canonical))
        state_edges = 0
        while pending:
            state = pending.popleft()
            successors = set(GrowingCalculation(graph, state).successors())
            state_edges += len(successors)
            for t in successors:
                if not satisfies_condition(t):
                    raise CheckFailure(f'a successor of {state} violates the bounds: {t}')
                if t not in states:
                    states.add(t)
                    pending.append(t)
                    if len(states) > state_limit:
                        raise CheckFailure('too many states')
        added = graph.edge_count() - edges_before
        report['explorations'].append({
            'history_vertices': graph.vertex_count(), 'history_edges': graph.edge_count(),
            'states': len(states), 'state_edges': state_edges, 'edges_added': added})
        if added == 0:
            break
    report['history_vertices'] = graph.vertex_count()
    report['history_edges'] = graph.edge_count()
    return {'graph': graph, 'report': report}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--memory', type=int, default=12, help='history length L')
    parser.add_argument('--start', type=int, default=30, help='start before column N')
    parser.add_argument('--output', type=Path, default=HERE / 'results' / 'constructed-history.json')
    args = parser.parse_args()
    result = construct(args.memory, args.start)
    graph, report = result['graph'], result['report']
    args.output.parent.mkdir(exist_ok=True)
    graph.save(args.output)
    for i, row in enumerate(report['explorations'], 1):
        print(f"exploration {i}: {row['history_vertices']} vertices, {row['history_edges']} edges, "
              f"{row['states']} states, {row['edges_added']} edges added")
    print('written:', args.output)
    if (args.memory, args.start) == (12, 30):
        same = json.loads(args.output.read_text()) == json.loads((HERE / 'history.json').read_text())
        print('identical to history.json:', same)


if __name__ == '__main__':
    main()
