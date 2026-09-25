"""Upper bounds for the corollary "Column runs and gaps" and the forbidden gap factors.

    python runs_and_gaps.py

Proof of the corollary "Column runs and gaps", first paragraph. Project each symbol s = 2u + b of
the queen word to its column bit u = s >> 1. By the induction of
Section 6.4, every twelve consecutive symbols sigma_i ... sigma_{i+11}
(i >= 1) form a vertex of the twelve-symbol history graph. This program
checks that no projected vertex contains 0000 or 111111. So among columns
1, 2, ... there are never four consecutive lower columns or six consecutive
upper columns: lower runs have length at most 3 (A275885), upper runs at most
5 (A275886), gaps between upper columns at most 4 (A275888), and gaps between
lower columns at most 6 (A275889). The origin, which these OEIS sequences
count as an upper column, is covered by the direct check in witnesses.py.

The same projection excludes the gap factors 11111, 2222, 33, 44, and 3213
of A275888: a gap word c_1 ... c_r between upper columns is the column
pattern 1 0^(c_1 - 1) 1 ... 1 0^(c_r - 1) 1, which has at most twelve
columns for each of these words, and none occurs in a projected vertex.

Proof of the corollary "Column runs and gaps", second paragraph (A275887). In the run graph of the
forty-symbol state graph (see graphs.py), the terms of A275885 after the
start are the labels of a walk. For c = 1, 2, 3, the edges labeled c form an
acyclic graph, so the lengths of the maximal runs of c's, bounded on both
sides by a different label, form a finite set L_c, computed exactly by
dynamic programming below. The result is
    L_1 = {1..9, 11},   L_2 = {1..6},   L_3 = {1},
so A275887 takes values in {1..9, 11}. With the twelve-symbol graph the
same calculation gives L_1 = {1..11}: it cannot exclude 10.

These are upper bounds. witnesses.py shows that every value is attained and
checks the runs that begin before the forty-symbol graph applies.
Output: results/runs-and-gaps.json.
"""
from __future__ import annotations

import json

import graphs
from graphs import RESULTS, require

FORBIDDEN_GAP_FACTORS = ['11111', '2222', '33', '44', '3213']
EXPECTED_RUN_LENGTHS = {1: [1, 2, 3, 4, 5, 6, 7, 8, 9, 11], 2: [1, 2, 3, 4, 5, 6], 3: [1]}


def column_pattern(gap_word: str) -> str:
    """The upper(1)/lower(0) column pattern of a word of gaps between upper
    columns, from the first upper column to the last."""
    return '1' + ''.join('0' * (int(c) - 1) + '1' for c in gap_word)


def check_history_patterns(graph: graphs.StateGraph) -> None:
    """No projected history-graph vertex contains 0000, 111111, or the column
    pattern of a forbidden gap factor."""
    patterns = ['0000', '111111'] + [column_pattern(w) for w in FORBIDDEN_GAP_FACTORS]
    for word in graph.history.edges:
        projected = ''.join(str(s >> 1) for s in word)
        for pattern in patterns:
            require(pattern not in projected, f'the history vertex {word} contains {pattern}')


def maximal_run_lengths(runs: dict[int, set[tuple[int, int]]], c: int) -> list[int]:
    """The possible lengths of a maximal run of the label c in a walk.

    Let E(v) be the set of numbers of c-edges that can follow v before the
    first edge with a different label:
        E(v) = {0 if an edge with a label other than c leaves v}
               union {1 + l : v --c--> t, l in E(t)}.
    The c-edges must form an acyclic graph (a c-cycle would allow runs of
    every length); then E is computed in reverse topological order. A
    maximal run starts at the target of an edge with a different label, so
    the answer is the union of E(v) over those targets, without 0.
    """
    same = {v: {t for t, k in runs[v] if k == c} for v in runs}
    order = graphs.topological_order(set(runs), lambda v: same[v])
    require(order is not None, f'the edges labeled {c} contain a cycle')
    E: dict[int, set[int]] = {}
    for v in reversed(order):
        E[v] = {0} if any(k != c for _, k in runs[v]) else set()
        for t in same[v]:
            E[v].update(1 + length for length in E[t])
    starts = {t for v in runs for t, k in runs[v] if k != c}
    return sorted(set().union(*(E[v] for v in starts)) - {0})


def analyse(graph: graphs.StateGraph) -> dict:
    gaps = graphs.gap_graph(graph)
    runs = graphs.run_graph(gaps)
    return {
        'gap graph vertices': len(gaps),
        'gap graph edges': sum(map(len, gaps.values())),
        'gap labels': sorted({k for edges in gaps.values() for _, k in edges}),
        'run graph vertices': len(runs),
        'run graph edges': sum(map(len, runs.values())),
        'run labels': sorted({k for edges in runs.values() for _, k in edges}),
        'maximal run lengths': {c: maximal_run_lengths(runs, c) for c in (1, 2, 3)},
    }


def run() -> list[str]:
    twelve, forty = graphs.twelve_symbol_graph(), graphs.forty_symbol_graph()
    check_history_patterns(twelve)
    results = {'12': analyse(twelve), '40': analyse(forty)}
    for result in results.values():
        require(result['gap labels'] == [1, 2, 3, 4], 'unexpected gap labels')
        require(result['run labels'] == [1, 2, 3], 'unexpected run labels')
    require(results['40']['maximal run lengths'] == EXPECTED_RUN_LENGTHS,
            'unexpected maximal run lengths in the forty-symbol run graph')
    require(results['12']['maximal run lengths'][1] == list(range(1, 12)),
            'the twelve-symbol graph should permit maximal runs of 1 of lengths 1..11')
    RESULTS.mkdir(exist_ok=True)
    output = {'forbidden gap factors': FORBIDDEN_GAP_FACTORS,
              'column patterns': {w: column_pattern(w) for w in FORBIDDEN_GAP_FACTORS},
              **{f'{m}-symbol graphs': r for m, r in results.items()}}
    (RESULTS / 'runs-and-gaps.json').write_text(json.dumps(output, indent=2) + '\n', newline='\n')
    L12, L40 = results['12']['maximal run lengths'], results['40']['maximal run lengths']
    return [
        'no 12-symbol history vertex contains 0000 or 111111 (upper columns)',
        'no 12-symbol history vertex contains the gap factors ' + ', '.join(FORBIDDEN_GAP_FACTORS),
        f'gap labels 1..4 in both gap graphs; 40-symbol run graph: '
        f'{results["40"]["run graph vertices"]} vertices, {results["40"]["run graph edges"]} edges',
        f'40-symbol maximal run lengths: L1 = {L40[1]}, L2 = {L40[2]}, L3 = {L40[3]}',
        f'12-symbol maximal run lengths: L1 = {L12[1]}, L2 = {L12[2]}, L3 = {L12[3]}',
    ]


def main() -> None:
    for line in run():
        print(line)
    print('written:', RESULTS / 'runs-and-gaps.json')


if __name__ == '__main__':
    main()
