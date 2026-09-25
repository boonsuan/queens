#!/usr/bin/env python3
"""Compare every coordinate of the C programs with an independent calculation.

The reference places each queen with complete occupancy arrays (rows,
diagonals and antidiagonals), and its first 3000 rows are checked against the
literal greedy rule.  Each program in build/ is run with --emit and every
"column row" line, and the JSON summary, is compared.  The command-line
interface of build/queens_fast is also checked on all counts 0..256, at
buffer boundaries, and on invalid arguments.

  python3 tests/check_coordinates.py [--count N] [--programs NAME ...]

Run `make all debug` first.  This is a finite test; correctness for all
columns is proved in Section 7.4 of the paper.
"""
from __future__ import annotations

import argparse
from array import array
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FNV0, FNV1, MASK = 14695981039346656037, 1099511628211, (1 << 64) - 1
PROGRAMS = ['queens_fast', 'queens_debug', 'queens_budget1',
            'local_rule_reference', 'knuth_packed']


def direct_prefix(count):
    """The literal greedy rule: the lowest row attacked by no earlier queen."""
    rows, differences, sums, out = set(), set(), set(), []
    for n in range(count):
        y = 0
        while y in rows or y - n in differences or y + n in sums:
            y += 1
        rows.add(y)
        differences.add(y - n)
        sums.add(y + n)
        out.append(y)
    return out


def occupancy_reference(count):
    """Rows q_0, ..., q_{count-1} from full occupancy arrays.

    m is the least unused row and d the least unused lower-diagonal
    magnitude.  Only rows m..n-d can hold a lower queen; if none is free,
    the queen is upper, in row n + U(n).
    """
    if not count:
        return
    rows, diag, sums = bytearray(2 * count + 2), bytearray(count + 2), bytearray(3 * count + 3)
    rows[0] = sums[0] = 1
    m, d, upper = 1, 1, 0
    yield 0
    for n in range(1, count):
        y = m
        while y <= n - d and (rows[y] or diag[n - y] or sums[n + y]):
            y += 1
        if y > n - d:
            upper += 1
            y = n + upper
        else:
            diag[n - y] = 1
            while diag[d]:
                d += 1
        assert not rows[y] and not sums[n + y]
        rows[y] = sums[n + y] = 1
        while rows[m]:
            m += 1
        yield y


def expected_summary(rows):
    h = FNV0
    for y in rows:
        h = ((h ^ y) * FNV1) & MASK
    n = len(rows)
    return {'count': n, 'last_column': n - 1 if n else None,
            'last_queen': rows[-1] if n else None, 'hash': f'{h:016x}'}


def compare_summary(actual, expected):
    for key in expected:
        assert actual[key] == expected[key], (key, actual, expected)


def compare_program(path, expected, summary):
    """Run `path --count N --emit` and compare every line with the reference."""
    with tempfile.TemporaryFile(mode='w+b') as output:
        run = subprocess.run([str(path), '--count', str(len(expected)), '--emit'],
                             stdout=output, stderr=subprocess.PIPE, check=True)
        output.seek(0)
        seen = 0
        for n, line in enumerate(output):
            column, row = map(int, line.split())
            assert column == n and n < len(expected) and row == expected[n], (path, n, row)
            seen += 1
    assert seen == len(expected)
    compare_summary(json.loads(run.stderr), summary)


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--count', type=int, default=1000000)
    parser.add_argument('--programs', nargs='+', default=PROGRAMS)
    args = parser.parse_args()
    assert args.count >= 3000
    started = time.perf_counter()
    expected = array('Q', occupancy_reference(args.count))
    assert list(expected[:3000]) == direct_prefix(3000)
    summary = expected_summary(expected)
    for name in args.programs:
        compare_program(ROOT / 'build' / name, expected, summary)

    # Small counts and counts at buffer boundaries, with and without --emit.
    fast = ROOT / 'build' / 'queens_fast'
    boundaries = sorted(set(range(257)) | {511, 512, 513, 1023, 1024, 1025, 2047, 2048,
                                           2049, 4095, 4096, 4097, 8191, 8192, 8193})
    for n in boundaries:
        wanted = expected_summary(expected[:n])
        compare_summary(json.loads(subprocess.check_output([str(fast), '--count', str(n)])), wanted)
        run = subprocess.run([str(fast), '--count', str(n), '--emit'], capture_output=True, check=True)
        assert run.stdout == b''.join(f'{i} {expected[i]}\n'.encode() for i in range(n))
        compare_summary(json.loads(run.stderr), wanted)

    invalid = [[], ['--count'], ['--count', '-1'], ['--count', '+1'], ['--count', ' 1'],
               ['--count', '1 '], ['--count', '1e6'], ['--count', ''], ['--count', str(1 << 63)],
               ['--count', '18446744073709551616'], ['--count', '1', '--count', '2'],
               ['--count', '1', '--emit', '--emit'], ['--unknown']]
    for arguments in invalid:
        result = subprocess.run([str(fast), *arguments], capture_output=True)
        assert result.returncode != 0, arguments

    # The executable needs no data files: run a copy from an empty directory.
    with tempfile.TemporaryDirectory() as directory:
        target = Path(directory) / 'generator'
        shutil.copyfile(fast, target)
        target.chmod(0o755)
        output = subprocess.check_output([str(target), '--count', str(args.count)], cwd=directory)
        compare_summary(json.loads(output), summary)

    print(json.dumps({'passed': True, 'coordinates_compared': args.count,
                      'programs': args.programs, 'direct_greedy_rows': 3000,
                      'summary': summary, 'boundary_counts': len(boundaries),
                      'invalid_arguments_rejected': len(invalid),
                      'seconds': round(time.perf_counter() - started, 1)}, indent=2))


if __name__ == '__main__':
    main()
