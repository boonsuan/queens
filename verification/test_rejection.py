"""Check that both verifiers reject a damaged history graph.

    python test_rejection.py

Removes one edge from a copy of history.json: the edge labeled 1 that leaves
the vertex sigma_18 ... sigma_29 = 300322301212 and carries the first new
symbol, sigma_30 = 1 (Section 6.2). The first step's output check then
fails, and each verifier must stop with an error.
"""
from __future__ import annotations

import json
import tempfile
from pathlib import Path

import verify_bitmasks as bitmasks
import verify_tuples as tuples
from calculation import CheckFailure, HistoryGraph, encode

HERE = Path(__file__).resolve().parent


def main() -> None:
    data = json.loads((HERE / 'history.json').read_text())
    vertex = encode((3, 0, 0, 3, 2, 2, 3, 0, 1, 2, 1, 2))
    for record in data['vertices']:
        if record[0] == vertex:
            assert record[1] & 0b10, 'the edge labeled 1 should be present'
            record[1] &= ~0b10
    with tempfile.TemporaryDirectory() as directory:
        damaged = Path(directory) / 'history.json'
        damaged.write_text(json.dumps(data))
        runs = {'verify_tuples': lambda: tuples.explore(HistoryGraph.load(damaged)),
                'verify_bitmasks': lambda: bitmasks.explore(bitmasks.read_graph(damaged))}
        for name, run in runs.items():
            try:
                run()
            except (CheckFailure, bitmasks.Failure) as failure:
                print(f'{name} rejects the graph: {failure}')
            else:
                raise SystemExit(f'{name} accepted the damaged graph')
    print('REJECTED BY BOTH')


if __name__ == '__main__':
    main()
