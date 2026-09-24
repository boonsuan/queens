"""An independent implementation of the exhaustive check of Section 6.3.

    python verify_bitmasks.py [history.json]

This program performs the same check as verify_tuples.py but shares no code
with it: it computes the starting board itself, packs the records into
integers, and handles branching with explicit work lists instead of
recursive generators. compare_verifiers.py checks that the two programs
reach the same states with the same successors.

A state is the tuple (w, z, R, D, A, uh, bh, uq, bq, qlen, hout):
    R, D, A    bit masks: bit a is set when offset a belongs to the set
    uh, bh     upper-column and upper-row bits of H_in; bit 0 is index m-12
               and bit 11 is index m-1
    uq, bq     the same bits of Q; bit h is index m+h
    qlen       the length of Q
    hout       H_out in base four, newest symbol in the lowest two bits
A queue is the triple (uq, bq, qlen).
"""
from __future__ import annotations

import json
import sys
from collections import deque
from pathlib import Path

L = 12                            # length of the two histories
WORD_MASK = (1 << 2 * L) - 1      # keeps the last twelve symbols of a base-four code
START = 30                        # the check starts before column 30


class Failure(RuntimeError):
    """A check failed; the verification stops."""


def require(condition, message):
    if not condition:
        raise Failure(message)


def read_graph(path):
    """Return {vertex code: mask of permitted next symbols}, checking that
    each vertex is listed once and every edge ends at a vertex."""
    data = json.loads(Path(path).read_text())
    require(data['memory'] == L, 'wrong history length')
    graph = {}
    for code, mask in data['vertices']:
        require(0 <= code <= WORD_MASK and 0 <= mask <= 15, 'invalid vertex record')
        require(code not in graph, 'a vertex is listed twice')
        graph[code] = mask
    for code, mask in graph.items():
        for s in range(4):
            if mask >> s & 1:
                require(((code << 2 | s) & WORD_MASK) in graph, 'an edge leaves the vertex list')
    return graph


def input_vertex(uh, bh, uq, bq, qlen):
    """The code of the last twelve symbols of H_in followed by Q."""
    code = 0
    for i in range(L):
        code = code << 2 | (uh >> i & 1) << 1 | (bh >> i & 1)
    for h in range(qlen):
        code = code << 2 | (uq >> h & 1) << 1 | (bq >> h & 1)
    return code & WORD_MASK


def within_bounds(s):
    """The bounds of Section 5.1: w <= 4, -4 <= z <= 5, R, D within [1..4]."""
    w, z, R, D = s[:4]
    return w <= 4 and -4 <= z <= 5 and R < 32 and not R & 1 and D < 32 and not D & 1


def starting_state(graph):
    """Compute and check the state before column 30 from the first 30 queens."""
    rows, diagonals, antidiagonals, q = set(), set(), set(), []
    for x in range(START):
        y = 0
        while y in rows or y - x in diagonals or y + x in antidiagonals:
            y += 1
        q.append(y)
        rows.add(y)
        diagonals.add(y - x)
        antidiagonals.add(y + x)
    u = [int(q[i] > i) for i in range(START)]
    b = [0] * START
    for x in range(START):
        if u[x] and q[x] < START:
            b[q[x]] = 1
    sym = [2 * u[i] + b[i] for i in range(START)]

    # sigma_1 ... sigma_29 follows the graph.
    code = 0
    for t in range(1, START):
        if t > L:
            require(graph.get(code, 0) >> sym[t] & 1, 'the starting word leaves the graph')
        code = (code << 2 | sym[t]) & WORD_MASK
        if t >= L:
            require(code in graph, 'a starting window is not a vertex')

    # |d_j - j| <= 4 for the lower queens before column 30.
    j = 0
    for x in range(START):
        if q[x] < x:
            j += 1
            require(abs(x - q[x] - j) <= 4, 'a starting lower queen has |d_j - j| > 4')

    m = min(set(range(1, START + 1)) - set(q))
    d = min(set(range(1, START + 1)) - {x - q[x] for x in range(START) if q[x] < x})
    kappa = sum(u[1:m])
    require(kappa >= 12 and m > L, 'the start is too early')
    R = D = A = 0
    for x in range(START):
        if q[x] < x:
            if q[x] >= m:
                R |= 1 << q[x] - m
            if x - q[x] >= d:
                D |= 1 << x - q[x] - d
            if x + q[x] >= START + m:
                A |= 1 << x + q[x] - START - m
    uh = sum(u[m - L + i] << i for i in range(L))
    bh = sum(b[m - L + i] << i for i in range(L))
    uq = sum(u[m + h] << h for h in range(START - m))
    bq = sum(b[m + h] << h for h in range(START - m))
    hout = 0
    for t in range(START - L, START):
        hout = hout << 2 | sym[t]
    s = (START - m - d, START - m - kappa, R, D, A, uh, bh, uq, bq, START - m, hout)
    require(within_bounds(s), 'the starting state violates the bounds')
    return s


def upper_columns(uh, uq, qlen):
    """For each stored upper column m + h: (relative row h + Gamma(h),
    relative antidiagonal index 2h + Gamma(h), whether h >= 0)."""
    columns = []
    gamma = 0
    for h in range(-1, -L - 1, -1):          # Gamma(h) = -(upper columns m+h+1 .. m-1)
        bit = uh >> (L + h) & 1
        if bit:
            columns.append((h - gamma, 2 * h - gamma, False))
        gamma += bit
    gamma = 0
    for h in range(qlen):                   # Gamma(h) = upper columns m .. m+h
        bit = uq >> h & 1
        gamma += bit
        if bit:
            columns.append((h + gamma, 2 * h + gamma, True))
    return columns


def adjustment(columns, x):
    """J(x): add the upper queens of Q at relative row <= x, subtract those of
    H_in at relative row > x."""
    added = sum(1 for row, _, in_queue in columns if in_queue and row <= x)
    removed = sum(1 for row, _, in_queue in columns if not in_queue and row > x)
    return added - removed


class Explorer:
    def __init__(self, graph):
        self.graph = graph
        self.stopped = 0
        self.choices = 0
        self.lower_choices = 0

    def extend(self, s, queue, length):
        """All queues reached from `queue` by requests until its length is at
        least `length`. A request at a vertex without edges ends that branch."""
        done, work = [], [queue]
        while work:
            uq, bq, qlen = work.pop()
            if qlen >= length:
                done.append((uq, bq, qlen))
                continue
            mask = self.graph[input_vertex(s[5], s[6], uq, bq, qlen)]
            if mask == 0:
                self.stopped += 1
                continue
            for sym in range(4):
                if mask >> sym & 1:
                    work.append((uq | (sym >> 1) << qlen, bq | (sym & 1) << qlen, qlen + 1))
        return done

    def successors(self, s):
        """The successor of every branch of the calculation on state s."""
        w, z, R, D, A, uh, bh, uq0, bq0, qlen0, hout = s
        result = set()

        # Choose the queen. Each item of `work` is (next candidate r, queue);
        # each choice is (r, queue), with r = None for an upper queen.
        choices = []
        work = [(0, queue) for queue in self.extend(s, (uq0, bq0, qlen0), z)]
        while work:
            r, queue = work.pop()
            if r > w:
                choices.append((None, queue))
                continue
            if R >> r & 1 or D >> (w - r) & 1 or A >> r & 1:
                work.append((r + 1, queue))
                continue
            for longer in self.extend(s, queue, 1 + max(r, (z + r) // 2)):
                columns = upper_columns(uh, longer[0], longer[2])
                attacked = longer[1] >> r & 1 or any(a == z + r for _, a, _ in columns)
                if attacked:
                    work.append((r + 1, longer))
                else:
                    choices.append((r, longer))

        for r, (uq, bq, qlen) in choices:
            self.choices += 1
            # Produce and check the new symbol.
            columns = upper_columns(uh, uq, qlen)
            b_out = adjustment(columns, z) - adjustment(columns, z - 1)
            sym = (0 if r is not None else 2) + b_out
            require(0 <= sym <= 3 and self.graph[hout] >> sym & 1, 'missing output edge')
            new_hout = (hout << 2 | sym) & WORD_MASK
            # Record a lower queen and find the diagonal advance nu.
            Rt, Dt, At = R, D, A
            if r is not None:
                self.lower_choices += 1
                Rt |= 1 << r
                Dt |= 1 << (w - r)
                At |= 1 << r
            nu = 0
            while Dt >> nu & 1:
                nu += 1
            # Find the row advance mu, making requests as needed.
            rows = [(0, (uq, bq, qlen))]
            while rows:
                h, queue = rows.pop()
                for longer in self.extend(s, queue, h + 1):
                    if Rt >> h & 1 or longer[1] >> h & 1:
                        rows.append((h + 1, longer))
                        continue
                    mu = h
                    moved = (1 << mu) - 1                 # the first mu symbols of Q
                    new_uh = ((uh | (longer[0] & moved) << L) >> mu) & ((1 << L) - 1)
                    new_bh = ((bh | (longer[1] & moved) << L) >> mu) & ((1 << L) - 1)
                    upper_moved = bin(longer[0] & moved).count('1')
                    t = (w + 1 - mu - nu, z + 1 - mu - upper_moved,
                         Rt >> mu, Dt >> nu, At >> (1 + mu),
                         new_uh, new_bh, longer[0] >> mu, longer[1] >> mu, longer[2] - mu,
                         new_hout)
                    require(within_bounds(t), 'a successor violates the bounds')
                    result.add(t)
        return result


def explore(graph):
    """Breadth-first exploration of the state graph from the state before column 30."""
    explorer = Explorer(graph)
    start = starting_state(graph)
    successors = {}
    pending = deque([start])
    seen = {start}
    while pending:
        s = pending.popleft()
        successors[s] = frozenset(explorer.successors(s))
        for t in successors[s]:
            if t not in seen:
                seen.add(t)
                pending.append(t)
    return start, successors, explorer


def canonical(s):
    """The encoding shared with verify_tuples.canonical."""
    w, z, R, D, A, uh, bh, uq, bq, qlen, hout = s
    hin = 0
    for i in range(L):
        hin = hin << 2 | (uh >> i & 1) << 1 | (bh >> i & 1)
    queue = 0
    for h in range(qlen):
        queue = queue << 2 | (uq >> h & 1) << 1 | (bq >> h & 1)
    return (w, z, R, D, A, hin, qlen, queue, hout)


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / 'history.json'
    graph = read_graph(path)
    _, successors, explorer = explore(graph)
    print('VERIFIED')
    print('history-graph vertices and edges:', len(graph),
          sum(bin(mask).count('1') for mask in graph.values()))
    print('state-graph vertices and edges:', len(successors),
          sum(map(len, successors.values())))
    print('completed choices:', explorer.choices)
    print('completed lower choices:', explorer.lower_choices)
    print('requests with no outgoing edge:', explorer.stopped)


if __name__ == '__main__':
    main()
