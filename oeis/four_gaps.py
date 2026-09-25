"""Distances between consecutive 4s in A275888 (Section 6.5).

    python four_gaps.py

Work in the gap graph of the forty-symbol state graph (graphs.py). The
first 4 of A275888 is the gap from column 4969 to column 4973 (witnesses.py),
far after the start before column 80, so every pair of consecutive 4s is
spelled by a path in the gap graph: it starts at the target of an edge
labeled 4, takes edges not labeled 4, and ends with an edge labeled 4. Its
distance, measured in terms of A275888 (not in columns), is the number of
edges after the first 4, the second 4 included.

Minimum distance. Breadth-first search from the targets of the 4-edges,
along edges not labeled 4, finds the shortest such path: 71 edges. So
consecutive 4s are at least 71 terms apart.

Unique fill. The program then lists every word spelled by such a path of
exactly 71 edges, from the first 4 to the second, both included. There is
only one:
    412111311132211131113221211223111122311112321113113112321113121212112214
so every pair of consecutive 4s at distance 71 has this fill. The pair at
indices 83418 and 83489 attains it (witnesses.py).

What is not proved. The graph also contains a cycle avoiding 4 that is
reachable from a 4 and from which a 4 can be reached. Going around it
repeatedly gives arbitrarily long paths from one 4 to the next, so the
graph gives no upper bound on the distance between consecutive 4s. This is
not a counterexample: the graph is an upper bound for the actual word, and
not every path is actual. It means only that this graph cannot prove the
proposed maximum distance (AUDIT.md). The program finds such a cycle and
records its labels.

Output: results/four-gaps.json.
"""
from __future__ import annotations

import json
from collections import deque

import graphs
from graphs import RESULTS, require

EXPECTED_FILL = '412111311132211131113221211223111122311112321113113112321113121212112214'


def minimum_distance(gaps, starts: set[int]) -> int:
    """The least number of edges from a start to the end of a 4-edge,
    avoiding 4 before the last edge (breadth-first search)."""
    distance = {v: 0 for v in starts}
    queue = deque(sorted(starts))
    while queue:
        v = queue.popleft()
        if any(k == 4 for _, k in gaps[v]):
            return distance[v] + 1
        for t, k in gaps[v]:
            if k != 4 and t not in distance:
                distance[t] = distance[v] + 1
                queue.append(t)
    raise graphs.CheckFailure('no path from a 4 to a 4')


def fills(gaps, starts: set[int], length: int) -> list[str]:
    """Every word spelled by a path of `length` edges from a start, whose
    last edge is the only one labeled 4, with the first 4 prepended."""
    # finish[r]: the vertices where such a path with r edges can begin.
    finish = [set(), {v for v in gaps if any(k == 4 for _, k in gaps[v])}]
    for r in range(2, length + 1):
        finish.append({v for v in gaps if any(k != 4 and t in finish[r - 1] for t, k in gaps[v])})
    # Extend all words together; each word keeps the set of vertices where it can end.
    words = {'4': starts & finish[length]}
    for j in range(1, length + 1):
        extended: dict[str, set[int]] = {}
        for word, vertices in words.items():
            for v in vertices:
                for t, k in gaps[v]:
                    last = j == length
                    if (k == 4) == last and (last or t in finish[length - j]):
                        extended.setdefault(word + str(k), set()).add(t)
        words = extended
    return sorted(words)


def cycle_avoiding_4(gaps, starts: set[int]) -> list[str] | None:
    """A cycle of edges not labeled 4, reachable from a start, from which a
    4-edge can be reached; return its labels, or None if there is none."""
    avoiding4 = {v: {t for t, k in gaps[v] if k != 4} for v in gaps}
    predecessors: dict[int, set[int]] = {v: set() for v in gaps}
    for v in gaps:
        for t in avoiding4[v]:
            predecessors[t].add(v)

    def closure(sources, step):
        found, pending = set(sources), list(sources)
        while pending:
            for t in step[pending.pop()]:
                if t not in found:
                    found.add(t)
                    pending.append(t)
        return found

    can_reach_4 = closure({v for v in gaps if any(k == 4 for _, k in gaps[v])}, predecessors)
    productive = closure(starts, avoiding4) & can_reach_4
    # Remove vertices without a predecessor (Kahn's algorithm); every vertex
    # left then has a predecessor left, and following predecessors must repeat.
    indegree = {v: len(predecessors[v] & productive) for v in productive}
    ready = [v for v in productive if indegree[v] == 0]
    remaining = set(productive)
    while ready:
        v = ready.pop()
        remaining.discard(v)
        for t in avoiding4[v] & productive:
            indegree[t] -= 1
            if indegree[t] == 0:
                ready.append(t)
    if not remaining:
        return None
    walk, seen = [min(remaining)], set()
    while walk[-1] not in seen:
        seen.add(walk[-1])
        walk.append(min(predecessors[walk[-1]] & remaining))
    cycle = walk[walk.index(walk[-1]):][::-1]        # forward order, first vertex repeated
    return [str(min(k for t, k in gaps[v] if t == w and k != 4)) for v, w in zip(cycle, cycle[1:])]


def run() -> list[str]:
    gaps = graphs.gap_graph(graphs.forty_symbol_graph())
    starts = {t for v in gaps for t, k in gaps[v] if k == 4}
    shortest = minimum_distance(gaps, starts)
    require(shortest == 71, f'the minimum distance between consecutive 4s is {shortest}, not 71')
    shortest_fills = fills(gaps, starts, shortest)
    require(shortest_fills == [EXPECTED_FILL], 'the fill at distance 71 is not the expected unique fill')
    cycle = cycle_avoiding_4(gaps, starts)
    require(cycle is not None, 'expected a cycle avoiding 4 that can reach a 4')
    RESULTS.mkdir(exist_ok=True)
    output = {'minimum distance': shortest, 'fills at the minimum distance': shortest_fills,
              'cycle avoiding 4': {'length': len(cycle), 'labels': ''.join(cycle)}}
    (RESULTS / 'four-gaps.json').write_text(json.dumps(output, indent=2) + '\n', newline='\n')
    return [
        f'minimum distance between consecutive 4s: {shortest}',
        f'unique fill at that distance: {shortest_fills[0]}',
        f'a cycle of length {len(cycle)} avoiding 4 is reachable from a 4 and can reach a 4, '
        f'so no maximum distance is certified',
    ]


def main() -> None:
    for line in run():
        print(line)
    print('written:', RESULTS / 'four-gaps.json')


if __name__ == '__main__':
    main()
