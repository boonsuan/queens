"""Check Spire against the Section 7 generator (run by `make check`).

For each N below, build/reference computes the first N rows one at a time with the generator
of ../fast_generator and prints their checksum, sum and last row; build/spire and
build/spire-rows must print the same. The sizes include the seed (the first 48 columns, made
directly), ranges split between four and more threads, and a run on one thread. At N = 10^9,
beyond the reference's quick reach, Spire and Spire-rows are compared with each other.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
def run(program, *args):
    path = os.path.join(HERE, 'build', program)
    if os.path.exists(path + '.exe'):
        path += '.exe'
    out = subprocess.run([path] + [str(a) for a in args], check=True, capture_output=True, text=True).stdout
    return json.loads(out)

failures = 0
def expect(label, got, want, keys):
    global failures
    bad = [k for k in keys if got[k] != want[k]]
    print('%-34s %s' % (label, 'ok' if not bad else 'DIFFERS in ' + ', '.join(bad)))
    failures += bool(bad)

for n in (1, 2, 30, 47, 48, 49, 1000, 5000, 100000, 10 ** 6, 10 ** 7, 10 ** 8):
    ref = run('reference', n)
    expect('spire N = %d' % n, run('spire', n), ref, ('last', 'poly63'))
    expect('spire-rows N = %d' % n, run('spire-rows', n), ref, ('last', 'poly63', 'rows_sum'))
ref = run('reference', 10 ** 7)
expect('spire N = 10^7, 1 thread, 12 ranges', run('spire', 10 ** 7, 1, 12), ref, ('last', 'poly63'))
expect('spire N = 10^7, 3 threads, 50 ranges', run('spire', 10 ** 7, 3, 50), ref, ('last', 'poly63'))
fast, rows = run('spire', 10 ** 9), run('spire-rows', 10 ** 9)
expect('spire and spire-rows, N = 10^9', rows, fast, ('last', 'poly63'))
print('all checks passed' if not failures else '%d checks failed' % failures)
sys.exit(1 if failures else 0)
