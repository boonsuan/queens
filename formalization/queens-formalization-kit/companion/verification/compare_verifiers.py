"""Check that the two verifiers compute the same state graph.

    python compare_verifiers.py [history.json]

Runs verify_tuples.py and verify_bitmasks.py, converts every state to a
common encoding, and checks that both reach the same states and that every
state has the same complete set of successors in both.
"""
from __future__ import annotations

import sys
from pathlib import Path

import verify_bitmasks as bitmasks
import verify_tuples as tuples
from calculation import HistoryGraph

HERE = Path(__file__).resolve().parent


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'history.json'
    _, from_tuples, _ = tuples.explore(HistoryGraph.load(path))
    _, from_bitmasks, _ = bitmasks.explore(bitmasks.read_graph(path))
    graph_t = {tuples.canonical(s): frozenset(map(tuples.canonical, t))
               for s, t in from_tuples.items()}
    graph_b = {bitmasks.canonical(s): frozenset(map(bitmasks.canonical, t))
               for s, t in from_bitmasks.items()}
    if len(graph_t) != len(from_tuples) or len(graph_b) != len(from_bitmasks):
        raise SystemExit('the common encoding merged two different states')
    if graph_t != graph_b:
        raise SystemExit('the two state graphs differ')
    print('IDENTICAL')
    print('states compared:', len(graph_t))
    print('directed edges compared:', sum(map(len, graph_t.values())))


if __name__ == '__main__':
    main()
