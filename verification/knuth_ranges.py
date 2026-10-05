"""The check behind Theorem 2 and Knuth's ranges (Section 6.6).

    python knuth_ranges.py [history.json]

Explores the state graph exactly as verify_tuples.py does. For a state S,
write Y(S) = w - |D| + 1 - z/phi. By the one-step error identity of
Section 6.6, before column n,

    eps(n-1) = Y(S_n) - eps(m-1)/phi,        eps(x) = U(x) - x/phi,

and the state before column m has output history H_in(S_n). The script

  1. computes window bounds lo(W), hi(W) on the vertices W of the history
     graph, each of which is the output history of some state (checked in
     step 2): it finds the extremal states by iterating the rounds
         lo(W) = min { Y(S) - hi(H_in S)/phi : H_out(S) = W },
         hi(W) = max { Y(S) - lo(H_in S)/phi : H_out(S) = W }
     in floating point, then solves the resulting linear equations exactly
     in Q(sqrt 5), following each chain of extremal states to its cycle;
  2. checks, in exact arithmetic, that every vertex of the history graph is
     an output history (so every H_in, a vertex, is one too), that the
     bounds are consistent (both inequalities above hold for every
     state), that the least unused row is at least 30 before column 49,
     that lo(W) <= eps(n-1) <= hi(W), W = sigma_{n-12..n-1}, for
     30 <= n <= 48, and that eps(x) lies between the least lo and the
     greatest hi for x <= 28;
  3. evaluates the bounds of Proposition 24. For an upper queen in column
     n, q_n - n phi = eps(n) lies within the window bounds of
     sigma_{n-11..n}, a window whose last symbol has column bit 1. For a
     lower queen at offset r,
         q_n - n/phi = r + 1/phi^2 - (z + eps(m-1))/phi,
     with eps(m-1) within the window bounds of H_in, at every lower choice
     of every state. It combines these bounds with the columns 1, ..., 48,
     and checks that the extremes are the constants of Theorem 2, which lie
     inside Knuth's ranges. It also checks that every lower choice has
     -4 <= w - r - |D| <= 2, the range of d_j - j stated in Section 6.6.

Only the checks in steps 2 and 3 matter for the proof; how the bounds were
found in step 1 does not.
"""
from __future__ import annotations

import sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import verify_tuples
from calculation import Calculation, CheckFailure, HistoryGraph
from greedy import greedy_queens, queen_word

HERE = Path(__file__).resolve().parent
FLOAT_PHI = (1 + 5 ** 0.5) / 2


class Q5:
    """An element a + b sqrt 5 of Q(sqrt 5), with exact rational a and b."""
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a, self.b = Fraction(a), Fraction(b)

    @staticmethod
    def of(x) -> Q5:
        return x if isinstance(x, Q5) else Q5(x)

    def __add__(self, other):
        o = Q5.of(other)
        return Q5(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -Q5.of(other)

    def __rsub__(self, other):
        return Q5.of(other) - self

    def __mul__(self, other):
        o = Q5.of(other)
        return Q5(self.a * o.a + 5 * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __truediv__(self, other):
        o = Q5.of(other)
        norm = o.a * o.a - 5 * o.b * o.b
        return self * Q5(o.a / norm, -o.b / norm)

    def sign(self) -> int:
        """The sign of a + b sqrt 5, decided exactly."""
        a, b = self.a, self.b
        if b == 0 or a == 0 or (a > 0) == (b > 0):
            v = a if b == 0 else b if a == 0 else a
            return (v > 0) - (v < 0)
        d = a * a - 5 * b * b       # opposite signs: compare |a| with |b| sqrt 5
        if d == 0:
            return 0
        return (1 if a > 0 else -1) if d > 0 else (1 if b > 0 else -1)

    def __lt__(self, other): return (self - other).sign() < 0
    def __le__(self, other): return (self - other).sign() <= 0
    def __eq__(self, other): return (self - Q5.of(other)).sign() == 0
    def __hash__(self): return hash((self.a, self.b))

    def __float__(self):
        return float(self.a) + float(self.b) * 5 ** 0.5

    def __repr__(self):
        return f'{self.a} + {self.b} sqrt5'


SQRT5 = Q5(0, 1)
PHI = (1 + SQRT5) / 2
INV_PHI = PHI - 1                  # 1/phi
INV_PHI2 = 1 - INV_PHI             # 1/phi^2

# The constants of Theorem 2 (Section 6.6), and the extreme window bounds,
# which ../spire/spire-at.md (F6) uses.
UPPER = ((19 * SQRT5 - 49) / 8, SQRT5 - 1)          # bounds on q_n - n phi
LOWER = (15 - 8 * SQRT5, 13 - 4 * SQRT5)            # bounds on q_n - n/phi
WINDOW = ((23 * SQRT5 - 61) / 8, SQRT5 - 1)         # least lo, greatest hi
START, DIRECT = 30, 49


def choices(graph: HistoryGraph, state) -> set:
    """The queen choices of all branches of a state: a lower offset r, or None."""
    calc = Calculation(graph, state)
    return {r for T in calc.extend_queue(state.Q, state.z) for r, _ in calc.choose_queen(T, 0)}


def window_bounds(states, Y, Yf):
    """The narrowest consistent window bounds, exactly (step 1), as maps from
    each vertex W (an output history) to lo(W) and hi(W) in Q(sqrt 5)."""
    groups = defaultdict(list)
    for s in states:
        groups[s.H_out].append(s)
    for s in states:
        if s.H_in not in groups:
            raise CheckFailure(f'the input history of {s} is no output history')
    lo = {W: 0.0 for W in groups}
    hi = {W: 0.0 for W in groups}
    for _ in range(400):            # (1/phi)^400 is far below double precision
        lo, hi = ({W: min(Yf[s] - hi[s.H_in] / FLOAT_PHI for s in groups[W]) for W in groups},
                  {W: max(Yf[s] - lo[s.H_in] / FLOAT_PHI for s in groups[W]) for W in groups})
    # Each node ('lo' or 'hi', W) is c + x * (the value of the next node), x = -1/phi,
    # with c = Y of its extremal state; follow each chain to its cycle and solve.
    step = {}
    for W in groups:
        s = min(groups[W], key=lambda s: Yf[s] - hi[s.H_in] / FLOAT_PHI)
        step['lo', W] = (Y[s], ('hi', s.H_in))
        s = max(groups[W], key=lambda s: Yf[s] - lo[s.H_in] / FLOAT_PHI)
        step['hi', W] = (Y[s], ('lo', s.H_in))
    x = -INV_PHI
    value = {}
    for start in step:
        path, position = [], {}
        node = start
        while node not in value and node not in position:
            position[node] = len(path)
            path.append(node)
            node = step[node][1]
        if node in position:                         # a new cycle
            cycle = path[position[node]:]
            total, factor = Q5(0), Q5(1)
            for v in cycle:
                total, factor = total + factor * step[v][0], factor * x
            value[node] = total / (1 - factor)
            path = path[:position[node]] + cycle[1:]
        for v in reversed(path):
            value[v] = step[v][0] + x * value[step[v][1]]
    LO = {W: value['lo', W] for W in groups}
    HI = {W: value['hi', W] for W in groups}
    for W in groups:
        if abs(float(LO[W]) - lo[W]) > 1e-9 or abs(float(HI[W]) - hi[W]) > 1e-9:
            raise CheckFailure('the exact solution disagrees with the iteration')
    return LO, HI


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'history.json'
    graph = HistoryGraph.load(path)
    initial, successors, stats = verify_tuples.explore(graph, START)
    states = list(successors)
    if {s.H_out for s in states} != set(graph.edges):
        raise CheckFailure('some vertex of the history graph is no output history')
    Y = {s: Q5(s.w - len(s.D) + 1) - s.z * INV_PHI for s in states}
    Yf = {s: float(Y[s]) for s in states}
    LO, HI = window_bounds(states, Y, Yf)

    # 2. Consistency, exactly, at every state.
    for s in states:
        if not LO[s.H_out] <= Y[s] - HI[s.H_in] * INV_PHI:
            raise CheckFailure(f'the lower window bound fails at {s}')
        if not Y[s] - LO[s.H_in] * INV_PHI <= HI[s.H_out]:
            raise CheckFailure(f'the upper window bound fails at {s}')
    if (min(LO.values()), max(HI.values())) != WINDOW:
        raise CheckFailure('the extreme window bounds differ from WINDOW')

    # 2. The start: m >= 30 before column 49, and the window bounds for 30 <= n <= 48.
    q = greedy_queens(DIRECT + 1)
    sigma = queen_word(q)
    U = [0]
    for i in range(1, len(q)):
        U.append(U[-1] + (q[i] > i))
    eps = lambda x: Q5(U[x]) - x * INV_PHI
    used = set(q[:DIRECT])
    if next(y for y in range(DIRECT + 1) if y not in used) < START:
        raise CheckFailure(f'the least unused row before column {DIRECT} is below {START}')
    for n in range(START, DIRECT):
        W = tuple(sigma[n - 12:n])
        if W not in LO or not LO[W] <= eps(n - 1) <= HI[W]:
            raise CheckFailure(f'the window bounds fail directly at column {n}')
    # Below the windows, eps(x) itself lies between the extreme window bounds,
    # so that they bound eps(x) for every x >= 0 (used by ../spire/spire-at.md, F6).
    for x in range(START - 1):
        if not WINDOW[0] <= eps(x) <= WINDOW[1]:
            raise CheckFailure(f'eps({x}) lies outside the extreme window bounds')

    # 3. The queens, as in Proposition 24: upper queens through the windows
    # whose last symbol has column bit 1, lower queens at every lower choice
    # of every state, then the columns before 49.
    upper = [b for W in LO if W[-1] >= 2 for b in (LO[W], HI[W])]
    lower = []
    for s in states:
        for r in choices(graph, s):
            if r is None:
                continue
            if not -4 <= s.w - r - len(s.D) <= 2:          # d_j - j, by Section 4.1
                raise CheckFailure(f'w - r - |D| leaves [-4, 2] at {s}, offset {r}')
            base = Q5(r) + INV_PHI2 - s.z * INV_PHI      # q_n - n/phi = base - eps(m-1)/phi
            lower += [base - HI[s.H_in] * INV_PHI, base - LO[s.H_in] * INV_PHI]
    upper += [q[n] - n * PHI for n in range(1, DIRECT) if q[n] > n]
    lower += [q[n] - n * INV_PHI for n in range(1, DIRECT) if q[n] < n]
    found = ((min(upper), max(upper)), (min(lower), max(lower)))
    if found != (UPPER, LOWER):
        raise CheckFailure(f'the bounds on the queens differ from Theorem 2: {found}')
    # Knuth's ranges, in 0-indexed form.
    if not (-2 + INV_PHI < UPPER[0] and UPPER[1] < 1 + INV_PHI
            and -3 - INV_PHI2 < LOWER[0] and LOWER[1] < 5 - INV_PHI2):
        raise CheckFailure("the bounds do not lie inside Knuth's ranges")

    print(f'states: {len(states)}; vertices with window bounds: {len(LO)}')
    print('window bounds: least lo = %.6f, greatest hi = %.6f' % tuple(map(float, WINDOW)))
    print('q_n - n phi, upper queens: (%.6f, %.6f)' % tuple(map(float, UPPER)))
    print('q_n - n/phi, lower queens: (%.6f, %.6f)' % tuple(map(float, LOWER)))
    print("All checks passed: Theorem 2 holds, and with it both halves of Knuth's ranges.")


if __name__ == '__main__':
    try:
        main()
    except CheckFailure as failure:
        sys.exit(f'CHECK FAILED: {failure}')
