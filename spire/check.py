"""Check Spire against the Section 7 generator (run by `make check`).

For each N below, build/reference computes the first N rows one at a time with the generator
of ../fast_generator and prints their checksum, sum and last row; build/spire and
build/spire-rows must print the same. The sizes include the seed (the first 48 columns, made
directly), ranges split between four and more threads, and a run on one thread. At N = 10^9,
beyond the reference's quick reach, Spire and Spire-rows are compared with each other.

build/spire-print must write exactly the reference's rows, as text and as binary, from the
start and from inside the sequence; build/spire-at must give the reference's single rows.
Beyond the reference, spire-at (single copies, one step at a time, with numbers of any size)
and spire-print (tower tables, 64-bit numbers) are two different programs: their rows must
agree up to 10^19, and agree with the last row that spire computes. Beyond 10^19 there is
only spire-at. There its rows must agree however its chain of copies is aimed (--walk D starts
the chain D columns early), and each row must lie as close to n phi or n / phi as the paper
proves (Section 6): 1 - 4/phi < q_n - n phi < 2/phi, or -2 - 4/phi < q_n - n / phi < 4 + 1/phi.
"""
import json
import os
from decimal import Decimal, getcontext
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
P, MASK = 1099511628211, (1 << 64) - 1
def program(name):
    path = os.path.join(HERE, 'build', name)
    return path + '.exe' if os.path.exists(path + '.exe') else path
def call(name, *args, discard=False):
    """Run a program; with discard, its standard output (rows we do not need) is thrown away."""
    command = [program(name)] + [str(a) for a in args]
    done = subprocess.run(command, stdout=subprocess.DEVNULL if discard else subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode:
        sys.exit('%s failed (exit status %d): %s' % (' '.join(command), done.returncode, done.stderr.decode().strip()))
    return done
def run(name, *args):
    return json.loads(call(name, *args).stdout)

failures = 0
def expect(label, got, want, keys=None):
    global failures
    bad = [k for k in keys if got[k] != want[k]] if keys else ([] if got == want else ['the rows'])
    print('%-44s %s' % (label, 'ok' if not bad else 'DIFFERS in ' + ', '.join(bad)))
    failures += bool(bad)

def summary(rows):
    """What reference prints for a list of rows: the checksum (mod 2^63), sum and last row."""
    H = s = 0
    for q in rows:
        H = (H * P + q) & MASK
        s += q
    return {'poly63': '%016x' % (H & (MASK >> 1)), 'rows_sum': '%016x' % (s & MASK), 'last': rows[-1]}
def printed(A, B, binary=False):
    """The rows spire-print writes for [A, B), and its summary."""
    done = call('spire-print', A, B, *(['--binary'] if binary else []))
    if binary:
        rows = list(struct.unpack('<%dQ' % (len(done.stdout) // 8), done.stdout))
    else:
        rows = [int(line) for line in done.stdout.split(b'\n')[:-1]]
    return rows, json.loads(done.stderr)

# The first N rows: spire and spire-rows against the reference.
for n in (1, 2, 30, 47, 48, 49, 1000, 5000, 100000, 10 ** 6, 10 ** 7, 10 ** 8):
    ref = run('reference', n)
    expect('spire N = %d' % n, run('spire', n), ref, ('last', 'poly63'))
    expect('spire-rows N = %d' % n, run('spire-rows', n), ref, ('last', 'poly63', 'rows_sum'))
ref = run('reference', 10 ** 7)
expect('spire N = 10^7, 1 thread, 12 ranges', run('spire', 10 ** 7, 1, 12), ref, ('last', 'poly63'))
expect('spire N = 10^7, 3 threads, 50 ranges', run('spire', 10 ** 7, 3, 50), ref, ('last', 'poly63'))
fast, rows = run('spire', 10 ** 9), run('spire-rows', 10 ** 9)
expect('spire and spire-rows, N = 10^9', rows, fast, ('last', 'poly63'))

# spire-print: every row written, as text and as binary.
N = 10 ** 6
ref = run('reference', N)
text, text_summary = printed(0, N)
expect('spire-print 0 10^6, the text', summary(text), ref, ('last', 'poly63', 'rows_sum'))
expect('spire-print 0 10^6, its summary', text_summary, ref, ('last', 'poly63', 'rows_sum'))
expect('spire-print 0 10^6 --binary', printed(0, N, True)[0], text)
for A, B in ((0, 0), (0, 1), (29, 49), (65530, 65540), (123457, N - 3), (N - 1, N)):
    expect('spire-print %d %d' % (A, B), printed(A, B)[0], text[A:B])
ref = run('reference', 10 ** 8)
expect('spire-print 0 10^8 --binary, its summary', json.loads(call('spire-print', 0, 10 ** 8, '--binary', discard=True).stderr), ref,
       ('last', 'poly63', 'rows_sum'))

# spire-at: single rows, against the reference, then far beyond it.
columns = (0, 1, 2, 29, 30, 47, 48, 49, 1000, 16383, 16384, 65535, 65536, 65537, 999999, 1234567, 9999999)
at = run('reference', 10 ** 7, *columns)['at']
single = [json.loads(line) for line in call('spire-at', *columns).stdout.splitlines()]
expect('spire-at, %d columns below 10^7' % len(columns), {str(r['n']): r['q'] for r in single}, at)
getcontext().prec = 1200
phi = (1 + Decimal(5).sqrt()) / 2
far = (10 ** 18, 10 ** 19 - 1, 2 ** 64 - 1, 2 ** 64, 2 ** 128 + 1, 10 ** 20, 10 ** 100, 3 ** 500, 10 ** 1000)
single += [json.loads(line) for line in call('spire-at', *far).stdout.splitlines()]
deviation = lambda r: r['q'] - r['n'] * (phi if r['near'] == 'n*phi' else 1 / phi)  # printed to 6 places
expect('spire-at, its deviations (up to 10^1000)', [abs(r['deviation'] - float(deviation(r))) < 2e-6 for r in single], [True] * len(single))
bounds = {'n*phi': (1 - 4 / phi, 2 / phi), 'n/phi': (-2 - 4 / phi, 4 + 1 / phi)}
expect('spire-at, within the bounds of Section 6', [bounds[r['near']][0] < deviation(r) < bounds[r['near']][1] for r in single], [True] * len(single))
aimed = [[json.loads(line)['q'] for line in call('spire-at', '--walk', lead, *far).stdout.splitlines()] for lead in (0, 1000, 10 ** 6)]
expect('spire-at, its chain aimed three ways', aimed[1:], aimed[:1] * 2)
last = run('spire', 10 ** 10 + 1)['last']
expect('spire-at 10^10 and spire N = 10^10 + 1', {'q': run('spire-at', 10 ** 10)['q']}, {'q': last}, ('q',))
for n in (10 ** 12, 10 ** 15, 10 ** 18, 10 ** 19 - 2 * 10 ** 6):
    rows, made = printed(n, n + 10 ** 6)
    picks = (n, n + 1, n + 54321, n + 10 ** 6 - 1)
    got = [json.loads(line)['q'] for line in call('spire-at', *picks).stdout.splitlines()]
    expect('spire-at and spire-print near %.0e' % n, got, [rows[p - n] for p in picks])
    # The checksum comes from the hash loop, not from the rows written: they must agree.
    expect('spire-print near %.0e, its summary' % n, made, summary(rows), ('last', 'poly63', 'rows_sum'))
    later = printed(n + 333333, n + 1333333)[0]  # ranges that start elsewhere
    expect('spire-print near %.0e, from elsewhere' % n, later[:10 ** 6 - 333333], rows[333333:])
print('all checks passed' if not failures else '%d checks failed' % failures)
sys.exit(1 if failures else 0)
