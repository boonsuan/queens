"""An independent second check of Theorem 2 and Knuth's ranges (Section 6.6).

    python knuth_ranges_bitmasks.py [history.json]

knuth_ranges.py performs this check on the state graph of verify_tuples.py.
This program shares no code with it and uses only verify_bitmasks.py for the
state graph; it also differs in method:

  * numbers are exact elements p + q phi of Q(phi), with phi^2 = phi + 1,
    instead of a + b sqrt 5;
  * the window bounds are found by exact policy iteration, with no
    floating-point step. With a(W) = -lo(W) and b(W) = hi(W), the equations
        a(W) = max { -Y(S) + b(H_in S)/phi : H_out(S) = W },
        b(W) = max {  Y(S) + a(H_in S)/phi : H_out(S) = W }
    are a maximization with factor 1/phi, so policy iteration reaches their
    exact solution in finitely many rounds;
  * the queen choices of every branch are recomputed in the bit-mask
    encoding, and the first 49 queens by a separate greedy loop.

It then checks that every vertex of the history graph is an output history,
consistency at every state, the start (with eps(x) for x <= 28 between the
extreme window bounds), the range -4 <= w - r - |D| <= 2 at every lower
choice, and that the bounds of Proposition 24 (on the windows whose last
symbol has column bit 1, and at every lower choice) give exactly the
constants of Theorem 2, inside Knuth's ranges.
"""
from __future__ import annotations

import sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from verify_bitmasks import (L, START, Failure, explore, read_graph, require,
                             upper_columns)

FIRST_LINKED = 49     # from this column on, m >= 30 (checked below)


class Phi:
    """p + q phi with rational p, q, where phi = (1 + sqrt 5)/2."""
    __slots__ = ('p', 'q')

    def __init__(self, p, q=0):
        self.p, self.q = Fraction(p), Fraction(q)

    def __add__(self, o):
        o = o if isinstance(o, Phi) else Phi(o)
        return Phi(self.p + o.p, self.q + o.q)

    def __sub__(self, o):
        o = o if isinstance(o, Phi) else Phi(o)
        return Phi(self.p - o.p, self.q - o.q)

    def __neg__(self):
        return Phi(-self.p, -self.q)

    def times(self, o):
        # (p + q phi)(r + s phi) = pr + qs + (ps + qr + qs) phi
        return Phi(self.p * o.p + self.q * o.q, self.p * o.q + self.q * o.p + self.q * o.q)

    def over_phi(self):
        """Division by phi: (p + q phi)(phi - 1) = (q - p) + p phi."""
        return Phi(self.q - self.p, self.p)

    def inverse(self):
        # The conjugate of p + q phi is p + q - q phi, and their product is
        # p^2 + pq - q^2.
        norm = self.p * self.p + self.p * self.q - self.q * self.q
        return Phi((self.p + self.q) / norm, -self.q / norm)

    def sign(self):
        """The sign of p + q phi = (p + q/2) + (q/2) sqrt 5, decided exactly."""
        a, b = 2 * self.p + self.q, self.q            # twice the value: a + b sqrt 5
        if a >= 0 and b >= 0:
            return int(a > 0 or b > 0)
        if a <= 0 and b <= 0:
            return -1
        d = a * a - 5 * b * b
        return 0 if d == 0 else (1 if (d > 0) == (a > 0) else -1)

    def __lt__(self, o): return (self - o).sign() < 0
    def __le__(self, o): return (self - o).sign() <= 0
    def __eq__(self, o): return (self - o).sign() == 0
    def __hash__(self): return hash((self.p, self.q))

    def __repr__(self):
        return f'{self.p} + {self.q} phi'


def from_sqrt5(a, b) -> Phi:
    """a + b sqrt 5, using sqrt 5 = 2 phi - 1."""
    return Phi(Fraction(a) - Fraction(b), 2 * Fraction(b))


# The extreme window bounds, and the constants of Theorem 2 (Section 6.6).
WINDOW = (from_sqrt5(Fraction(-61, 8), Fraction(23, 8)), from_sqrt5(-1, 1))
UPPER = (from_sqrt5(Fraction(-49, 8), Fraction(19, 8)), from_sqrt5(-1, 1))
LOWER = (from_sqrt5(15, -8), from_sqrt5(13, -4))
INV_PHI = Phi(-1, 1)                  # 1/phi = phi - 1
INV_PHI2 = Phi(2, -1)                 # 1/phi^2 = 1 - 1/phi


def hin_code(uh, bh):
    """H_in as a vertex code of the history graph, from its column and row bit masks."""
    code = 0
    for i in range(L):
        code = code << 2 | (uh >> i & 1) << 1 | (bh >> i & 1)
    return code


def queen_choices(explorer, s):
    """The lower offset r, or None for an upper queen, of every branch."""
    w, z, R, D, A, uh, bh, uq, bq, qlen, hout = s
    found = set()
    work = [(0, queue) for queue in explorer.extend(s, (uq, bq, qlen), z)]
    while work:
        r, queue = work.pop()
        if r > w:
            found.add(None)
            continue
        if R >> r & 1 or D >> (w - r) & 1 or A >> r & 1:
            work.append((r + 1, queue))
            continue
        for longer in explorer.extend(s, queue, 1 + max(r, (z + r) // 2)):
            columns = upper_columns(uh, longer[0], longer[2])
            if longer[1] >> r & 1 or any(a == z + r for _, a, _ in columns):
                work.append((r + 1, longer))
            else:
                found.add(r)
    return found


def evaluate(policy, constant):
    """Values of the nodes under a policy: value(v) = constant[v] + value(next)/phi."""
    value = {}
    for start in policy:
        path, seen = [], {}
        v = start
        while v not in value and v not in seen:
            seen[v] = len(path)
            path.append(v)
            v = policy[v]
        if v in seen:                                  # close a cycle
            cycle = path[seen[v]:]
            total, factor = Phi(0), Phi(1)
            for u in cycle:
                total = total + factor.times(constant[u])
                factor = factor.over_phi()
            value[v] = total.times((Phi(1) - factor).inverse())
            path = path[:seen[v]] + cycle[1:]
        for u in reversed(path):
            value[u] = constant[u] + value[policy[u]].over_phi()
    return value


def window_bounds(states, Y):
    """Exact policy iteration for a = -lo and b = hi on the vertices of the
    history graph, each of them an output history."""
    groups = defaultdict(list)
    for s in states:
        groups[s[10]].append(s)
    for s in states:
        require(hin_code(s[5], s[6]) in groups, 'an input history is no output history')
    # Options of node ('a', W): states S with H_out = W, constant -Y(S), next ('b', H_in S);
    # options of ('b', W): constant Y(S), next ('a', H_in S).
    options = {}
    for W, members in groups.items():
        options['a', W] = [(-Y[s], ('b', hin_code(s[5], s[6]))) for s in members]
        options['b', W] = [(Y[s], ('a', hin_code(s[5], s[6]))) for s in members]
    choice = {v: 0 for v in options}
    rounds = 0
    while True:
        rounds += 1
        policy = {v: options[v][choice[v]][1] for v in options}
        constant = {v: options[v][choice[v]][0] for v in options}
        value = evaluate(policy, constant)
        changed = False
        for v, opts in options.items():
            current = constant[v] + value[policy[v]].over_phi()
            best = choice[v]
            for k, (c, nxt) in enumerate(opts):
                if current < c + value[nxt].over_phi():
                    best, current = k, c + value[nxt].over_phi()
            if best != choice[v]:
                choice[v], changed = best, True
        if not changed:
            break
    lo = {W: -value['a', W] for W in groups}
    hi = {W: value['b', W] for W in groups}
    return lo, hi, rounds


def first_queens(count):
    """q_0, ..., q_{count-1}, by the greedy rule (separate from the verifiers' copies)."""
    rows, diagonals, antidiagonals, q = set(), set(), set(), []
    for x in range(count):
        y = 0
        while y in rows or y - x in diagonals or y + x in antidiagonals:
            y += 1
        q.append(y)
        rows.add(y)
        diagonals.add(y - x)
        antidiagonals.add(y + x)
    return q


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / 'history.json'
    graph = read_graph(path)
    _, successors, explorer = explore(graph)
    states = list(successors)
    require({s[10] for s in states} == set(graph), 'some vertex of the history graph is no output history')
    Y = {s: Phi(s[0] - bin(s[3]).count('1') + 1) - Phi(s[1]).times(INV_PHI) for s in states}
    lo, hi, rounds = window_bounds(states, Y)

    # Consistency at every state.
    for s in states:
        V, W = hin_code(s[5], s[6]), s[10]
        require(lo[W] <= Y[s] - hi[V].over_phi(), f'the lower window bound fails at {s}')
        require(Y[s] - lo[V].over_phi() <= hi[W], f'the upper window bound fails at {s}')
    require((min(lo.values()), max(hi.values())) == WINDOW, 'the window extremes differ from WINDOW')

    # The start, from the first 49 queens.
    q = first_queens(FIRST_LINKED + 1)
    used = set(q[:FIRST_LINKED])
    require(min(set(range(FIRST_LINKED + 1)) - used) >= START, 'm < 30 before column 49')
    upper_count = [0]
    for i in range(1, len(q)):
        upper_count.append(upper_count[-1] + (q[i] > i))
    epsilon = lambda x: Phi(upper_count[x]) - Phi(x).times(INV_PHI)
    u = [int(q[i] > i) for i in range(len(q))]
    b = [0] * len(q)
    for x in range(len(q)):
        if u[x] and q[x] < len(q):
            b[q[x]] = 1
    for n in range(START, FIRST_LINKED):
        W = 0
        for t in range(n - L, n):
            W = W << 2 | 2 * u[t] + b[t]
        require(W in lo and lo[W] <= epsilon(n - 1) <= hi[W], f'the window bounds fail at column {n}')
    for x in range(START - 1):              # below the windows: eps(x) within the extremes
        require(WINDOW[0] <= epsilon(x) <= WINDOW[1], f'eps({x}) lies outside the extreme window bounds')

    # The queens, as in Proposition 24: upper queens through the windows whose
    # last symbol (the low two bits) has column bit 1, lower queens at every
    # lower choice of every state, then the columns before 49.
    upper = [x for W in lo if W & 2 for x in (lo[W], hi[W])]
    lower = []
    for s in states:
        V = hin_code(s[5], s[6])
        for r in queen_choices(explorer, s):
            if r is None:
                continue
            discrepancy = s[0] - r - bin(s[3]).count('1')
            require(-4 <= discrepancy <= 2, f'w - r - |D| = {discrepancy} at {s}')
            base = Phi(r) + INV_PHI2 - Phi(s[1]).times(INV_PHI)    # minus eps(m-1)/phi
            lower += [base - hi[V].over_phi(), base - lo[V].over_phi()]
    upper += [Phi(q[n]) - Phi(n).times(Phi(0, 1)) for n in range(1, FIRST_LINKED) if q[n] > n]
    lower += [Phi(q[n]) - Phi(n).times(INV_PHI) for n in range(1, FIRST_LINKED) if q[n] < n]
    found = ((min(upper), max(upper)), (min(lower), max(lower)))
    require(found == (UPPER, LOWER), f'the bounds on the queens differ from Theorem 2: {found}')
    require(Phi(-2) + INV_PHI < UPPER[0] and UPPER[1] < Phi(1) + INV_PHI
            and Phi(-3) - INV_PHI2 < LOWER[0] and LOWER[1] < Phi(5) - INV_PHI2,
            "the bounds do not lie inside Knuth's ranges")

    print(f'states: {len(states)}; vertices with window bounds: {len(lo)}; '
          f'policy-iteration rounds: {rounds}')
    print('All checks passed: Theorem 2 holds, and with it both halves of Knuth\'s ranges.')


if __name__ == '__main__':
    try:
        main()
    except Failure as failure:
        sys.exit(f'CHECK FAILED: {failure}')
