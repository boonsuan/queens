#!/usr/bin/env python3
"""Finite checks of build/scan_bounds, the scanner of Knuth's ranges.

For the first million queens, the rows printed by build/knuth_packed (whose
first 3000 rows are also checked against the literal greedy rule) are
scanned here in Python with exact arithmetic.  The scanner's counts,
extrema, witnesses, checksum and progress records must agree at fourteen
counts.  A test driver then feeds the scanner's comparison code synthetic
points close to the irrational interval ends, to exercise the exact integer
fallback, and checks its sign test on 12289 cases against Python integers
and 80-digit decimal arithmetic.

  make build/scan_bounds build/knuth_packed
  python3 tests/check_bounds.py

The driver is compiled with `cc`, which must support 128-bit integers.
"""
from __future__ import annotations
import argparse
import copy
from decimal import Decimal, localcontext
import json
import math
from pathlib import Path
import random
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FNV0, FNV1, MASK = 14695981039346656037, 1099511628211, (1 << 64) - 1
MAX_COUNT = 100000000000

DRIVER = r'''
#define main scanner_main
#include "scan_bounds.c"
#undef main
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (!strcmp(argv[1], "sign")) {
        int64_t a,b;
        while (scanf("%" SCNd64 " %" SCNd64, &a, &b) == 2)
            printf("%d\n", bounds_sign(a,b));
        return ferror(stdin) ? 1 : 0;
    }
    Scan scan = {0};
    scan.error = nextafter((double)MAX_COUNT * 0x1p-50 + 0x1p-48, INFINITY);
    scan.lower_lo = nextafter(-3 + scan.error, INFINITY);
    scan.lower_hi = nextafter(5 - scan.error, -INFINITY);
    scan.upper_lo = nextafter(-2 + scan.error, INFINITY);
    scan.upper_hi = nextafter(1 - scan.error, -INFINITY);
    scan.hash = UINT64_C(14695981039346656037);
    scan.started = clock(); timespec_get(&scan.wall_started, TIME_UTC);
    uint64_t c,s;
    while (scanf("%" SCNu64 " %" SCNu64, &c, &s) == 2) {
        process(&scan,c,s);
        scan.hash = (scan.hash ^ (s-1)) * UINT64_C(1099511628211);
        scan.last = s-1; ++scan.count;
    }
    QFGenerator *g=qf_create();
    if (!g) return 1;
    int result = report(stdout,&scan,g,1);
    qf_destroy(g); return result;
}
'''


def sign(a, b):
    """Sign of a-b sqrt(5), using isqrt rather than the C squared comparison."""
    if b == 0:
        return (a > 0) - (a < 0)
    if b < 0:
        return -sign(-a, -b)
    if a <= 0:
        return -1
    return 1 if a > math.isqrt(5 * b * b) else -1


def a_value(c, s, upper):
    return 2 * s + (-c if upper else c)


def compare(left, right, upper):
    c, s = left
    d, t = right
    return sign(a_value(c, s, upper) - a_value(d, t, upper), c - d)


def inside(c, s, upper):
    low, high = (-2, 1) if upper else (-3, 5)
    a = a_value(c, s, upper)
    return sign(a - 2 * low, c) >= 0 and sign(a - 2 * high, c) <= 0


def empty_expected():
    branch = dict(count=0, minimum=None, maximum=None,
                  branch_interval_violations=0, first_branch_violation=None)
    return dict(count=0, hash=FNV0, last_column=None, last_queen=None,
                upper=copy.deepcopy(branch), lower=copy.deepcopy(branch),
                origin_count=0, union_violations=0, first_union_violation=None)


def add_point(expected, c, s):
    expected['hash'] = ((expected['hash'] ^ (s - 1)) * FNV1) & MASK
    expected['count'] += 1
    expected['last_column'] = expected['count'] - 1
    expected['last_queen'] = s - 1
    if c == 1:
        expected['origin_count'] += 1
        assert s == 1 and inside(c, s, 0) and inside(c, s, 1)
        return
    upper = s > c
    branch = expected['upper' if upper else 'lower']
    point = (c, s)
    if branch['minimum'] is None or compare(point, branch['minimum'], upper) < 0:
        branch['minimum'] = point
    if branch['maximum'] is None or compare(point, branch['maximum'], upper) > 0:
        branch['maximum'] = point
    branch['count'] += 1
    if not inside(c, s, upper):
        if not branch['branch_interval_violations']:
            branch['first_branch_violation'] = point
        branch['branch_interval_violations'] += 1
        if not inside(c, s, not upper):
            if not expected['union_violations']:
                expected['first_union_violation'] = point
            expected['union_violations'] += 1


def check_witness(actual, expected, upper):
    if expected is None:
        assert actual is None, actual
        return
    assert (actual['c'], actual['s']) == expected, (actual, expected)
    with localcontext() as context:
        context.prec = 80
        c, s = map(Decimal, expected)
        phi = (Decimal(5).sqrt() + 1) / 2
        exact = s - c * (phi if upper else phi - 1)
        delta = abs(Decimal(str(actual['deviation'])) - exact)
        assert delta < Decimal(str(actual['display_error_bound'])), (delta, actual)


def check_summary(actual, expected):
    for key in ('count', 'last_column', 'last_queen', 'origin_count', 'union_violations'):
        assert actual[key] == expected[key], (key, actual[key], expected[key])
    assert actual['hash'] == '{:016x}'.format(expected['hash'])
    for upper, name in ((True, 'upper'), (False, 'lower')):
        want, got = expected[name], actual[name]
        for key in ('count', 'branch_interval_violations'):
            assert got[key] == want[key], (key, got, want)
        for key in ('minimum', 'maximum', 'first_branch_violation'):
            check_witness(got[key], want[key], upper)
    first = expected['first_union_violation']
    check_witness(actual['first_union_violation'], first, first and first[1] > first[0])


def direct_prefix(count):
    rows, differences, sums, answer = set(), set(), set(), []
    for n in range(count):
        y = 0
        while y in rows or y-n in differences or y+n in sums:
            y += 1
        rows.add(y); differences.add(y-n); sums.add(y+n); answer.append(y)
    return answer


def check_math(driver):
    rng = random.Random(6172026)
    cases = [(a, b) for a in range(-8, 9) for b in range(-8, 9)]
    for _ in range(1000):
        b = rng.randint(1, 2 * MAX_COUNT)
        centre = math.isqrt(5 * b * b)
        for shift in (-1, 0, 1):
            for flip_a, flip_b in ((1, 1), (-1, 1), (1, -1), (-1, -1)):
                cases.append((flip_a * (centre + shift), flip_b * b))
    text = ''.join('{} {}\n'.format(a, b) for a, b in cases)
    got = list(map(int, subprocess.check_output([str(driver), 'sign'], input=text.encode()).split()))
    with localcontext() as context:
        context.prec = 80
        sqrt5 = Decimal(5).sqrt()
        for (a, b), found in zip(cases, got):
            value = Decimal(a) - Decimal(b) * sqrt5
            assert found == (value > 0) - (value < 0) == sign(a, b), (a, b, found)
    assert len(got) == len(cases)
    sqrt5_x80 = (146542 << 64) | 0xf372fe94f82be739
    assert sqrt5_x80 == math.isqrt(5 << 160)
    return len(cases)


def synthetic_points():
    rng = random.Random(23092026)
    points = [(1, 1), (2, 2), (2, 5), (3, 2), (2, 1), (2, 6)]
    # The intentionally synthetic diagonal point tests the filter arithmetic;
    # production rejects non-origin diagonal queens before process().
    columns = [MAX_COUNT, MAX_COUNT-1, 1000000000, 100, 101]
    f, g = 1, 1
    while g <= MAX_COUNT:
        if g >= 100:
            columns.extend((g-1, g, g+1))
        f, g = g, f+g
    columns += [rng.randint(100, MAX_COUNT) for _ in range(1000)]
    with localcontext() as context:
        context.prec = 80
        phi = (Decimal(5).sqrt() + 1) / 2
        for c in columns:
            for slope in (phi, phi-1):
                central_row = int(c * slope)
                for shift in range(-4, 7):
                    points.append((c, central_row + shift))
    tail = points[6:]
    rng.shuffle(tail)
    points[6:] = tail
    return points


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--count', type=int, default=1000000)
    args = parser.parse_args()
    assert args.count >= 10000
    started = time.perf_counter()
    scanner, packed = ROOT/'build/scan_bounds', ROOT/'build/knuth_packed'
    wanted_counts = {0, 1, 2, 3, 30, 41, 1023, 1024, 1025, 2048, 3072, 4096, 4097, args.count}
    snapshots = {0: empty_expected()}
    expected = empty_expected()
    direct = direct_prefix(3000)
    with tempfile.TemporaryFile(mode='w+b') as output:
        run = subprocess.run([str(packed), '--count', str(args.count), '--emit'],
                             stdout=output, stderr=subprocess.PIPE, check=True)
        output.seek(0)
        seen = 0
        for n, line in enumerate(output):
            column, row = map(int, line.split())
            assert column == n
            if n < len(direct):
                assert row == direct[n], (n, row, direct[n])
            add_point(expected, n+1, row+1)
            seen += 1
            if seen in wanted_counts:
                snapshots[seen] = copy.deepcopy(expected)
        assert seen == args.count
        assert json.loads(run.stderr)['hash'] == '{:016x}'.format(expected['hash'])
    for count in sorted(wanted_counts):
        actual = json.loads(subprocess.check_output([str(scanner), '--count', str(count)]))
        check_summary(actual, snapshots[count])
    run = subprocess.run([str(scanner), '--count', '4097', '--progress-every', '1024'],
                         capture_output=True, check=True)
    for line in run.stderr.splitlines():
        actual = json.loads(line)
        check_summary(actual, snapshots[actual['count']])
        assert actual['final'] is False
    check_summary(json.loads(run.stdout), snapshots[4097])
    invalid = [[], ['--count', '-1'], ['--count', '1e11'], ['--count', str(MAX_COUNT+1)],
               ['--count', '1', '--progress-every', '0'], ['--count', '1', '--count', '2']]
    for argv in invalid:
        assert subprocess.run([str(scanner), *argv], capture_output=True).returncode != 0
    with tempfile.TemporaryDirectory() as folder:
        driver = Path(folder)/'bounds-test-driver'
        source = Path(folder)/'driver.c'
        source.write_text(DRIVER)
        subprocess.run(['cc', '-O2', '-std=c11', '-DNDEBUG', '-I'+str(ROOT/'src'),
                        str(source), str(ROOT/'src/queens_fast.c'), '-lm', '-o', str(driver)], check=True)
        sign_cases = check_math(driver)
        points = synthetic_points()
        expected_synthetic = empty_expected()
        for c, s in points:
            add_point(expected_synthetic, c, s)
        text = ''.join('{} {}\n'.format(c, s) for c, s in points)
        actual = json.loads(subprocess.check_output([str(driver), 'scan'], input=text.encode()))
        check_summary(actual, expected_synthetic)
        assert actual['exact_comparisons'] > 2
    report = dict(passed=True, scope='Finite regression, not an infinite proof',
                  knuth_packed_reference_rows=args.count, direct_greedy_rows=len(direct),
                  exact_signed_sqrt5_cases=sign_cases, synthetic_points=len(points),
                  synthetic_exact_comparisons=actual['exact_comparisons'],
                  exact_extrema_and_union_counts_match=True,
                  count_cases=sorted(wanted_counts), progress_checkpoints_checked=4,
                  invalid_cli_cases=len(invalid),
                  fixed_point_sqrt5_constant_checked=True,
                  seconds=round(time.perf_counter()-started, 1))
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
