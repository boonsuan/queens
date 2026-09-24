"""Repeat the construction with history lengths 4 through 14 (Section 6.2).

    python history_length_experiment.py

For each length L, run construct_history_graph.py with histories of length L,
the same start before column 30, the same calculation, and the same bounds
of Section 5. A length fails when the construction reaches a successor
violating the bounds; the violating state is recorded. A graph that closes is
checked again, with its edges fixed, by the exhaustive check of
verify_tuples.py. Lengths below 4 are not tried: since z >= -4, the upper
tests can involve the upper-column bits of columns m-4, ..., m-1, so the
input history must contain them.

Result: lengths 4 through 11 fail and 12, 13, 14 close. The results are
written to results/history-length-experiment.json.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

import verify_tuples
from calculation import CheckFailure
from construct_history_graph import construct

HERE = Path(__file__).resolve().parent


def main() -> None:
    rows = []
    for memory in range(4, 15):
        started = time.monotonic()
        try:
            graph = construct(memory, 30, state_limit=300_000)['graph']
        except CheckFailure as failure:
            rows.append({'memory': memory, 'result': 'fails', 'reason': str(failure)})
        else:
            _, successors, _ = verify_tuples.explore(graph)
            rows.append({'memory': memory, 'result': 'closes',
                         'history_vertices': graph.vertex_count(),
                         'history_edges': graph.edge_count(),
                         'states': len(successors),
                         'state_edges': sum(map(len, successors.values()))})
        rows[-1]['seconds'] = round(time.monotonic() - started, 1)
        print(json.dumps(rows[-1]), flush=True)
    output = HERE / 'results' / 'history-length-experiment.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(rows, indent=2) + '\n', newline='\n')


if __name__ == '__main__':
    main()
