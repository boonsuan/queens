#!/usr/bin/env python3
"""Measure generation and hashing time and peak memory (the timing table of Section 7.5).

For each count N and each program, the program is run as
`build/PROGRAM --count N` in a fresh process: once as an excluded warmup and
then --repeats times, alternating the order of the programs.  Each run is
started by the native launcher build/benchmark_native, which pins it to one
CPU and reports the elapsed CLOCK_MONOTONIC time from fork to wait4 and the
kernel's peak resident set size.  Runs are strictly sequential.

  make all build/benchmark_native
  python3 bench/run_benchmark.py --cpu 2 --output results/new-benchmark.json \\
      --counts 1000000 10000000 100000000 1000000000 10000000000

The JSON output holds the environment, every run (launcher statistics and
the program's summary line), and the median, minimum and maximum of each
time for every program and count; a CSV of those aggregates is written next
to it.  All runs at the same count must agree on the last row and checksum.
Check the output with tests/check_ec2_results.py.  Linux only.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FLAGS = '-O3 -std=c11 -DNDEBUG -fwrapv -Wall -Wextra -Wpedantic'   # make's default


def command(*args):
    r = subprocess.run(args, capture_output=True, text=True)
    return {'command': list(args), 'returncode': r.returncode,
            'stdout': r.stdout, 'stderr': r.stderr}


def environment(cpu):
    files = ['/proc/meminfo', '/sys/fs/cgroup/cpu.max', '/sys/fs/cgroup/memory.max']
    return {'timestamp_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
            'platform': platform.platform(), 'python': platform.python_version(),
            'cpu_affinity': sorted(os.sched_getaffinity(0)), 'pinned_cpu': cpu,
            'compiler': command('cc', '--version'), 'kernel': command('uname', '-a'),
            'lscpu': command('lscpu', '--json'),
            'system_files': {p: Path(p).read_text() for p in files if Path(p).exists()},
            'flags': FLAGS, 'isa_flags': 'none; no -march=native',
            'measurement_backend': 'Linux native CLOCK_MONOTONIC/wait4 launcher, bench/benchmark_native.c'}


def invoke(program, count, cpu):
    """One measured run of build/PROGRAM --count COUNT."""
    with tempfile.TemporaryDirectory() as directory:
        stats = Path(directory) / 'native.json'
        args = [str(ROOT / 'build/benchmark_native'), str(stats), '0', str(cpu), '--',
                str(ROOT / 'build' / program), '--count', str(count)]
        begin = time.perf_counter_ns()
        run = subprocess.run(args, capture_output=True, check=True)
        driver_wall = (time.perf_counter_ns() - begin) / 1e9
        resources = json.loads(stats.read_text())
    assert resources['returncode'] == 0 and not resources['timed_out']
    assert run.stderr == b'', run.stderr
    summary = json.loads(run.stdout)
    assert summary['count'] == count and summary['last_column'] == count - 1
    return {'wall_seconds': resources['wall_seconds'],
            'driver_wall_seconds': driver_wall,
            'generation_cpu_seconds': summary['seconds'],
            'resources': resources, 'summary': summary}


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--counts', nargs='+', type=int,
                        default=[10**6, 10**7, 10**8, 10**9, 10**10])
    parser.add_argument('--programs', nargs='+', default=['queens_fast', 'knuth_packed'])
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--cpu', type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument('--output', type=Path, default=ROOT / 'results/new-benchmark.json')
    args = parser.parse_args()
    assert args.repeats >= 1 and min(args.counts) >= 1
    assert args.cpu in os.sched_getaffinity(0)
    if args.output.exists():
        parser.error(f'{args.output} exists; choose a new --output')
    os.sched_setaffinity(0, {args.cpu})
    report = {'environment': environment(args.cpu),
              'arguments': {'counts': args.counts, 'programs': args.programs,
                            'repeats': args.repeats, 'cpu': args.cpu,
                            'output': str(args.output)},
              'warmups': [], 'runs': []}
    signatures = {}

    def record(program, count, repetition):
        row = {'program': program, 'count': count, 'repetition': repetition,
               **invoke(program, count, args.cpu)}
        signature = tuple(row['summary'][k] for k in ('last_queen', 'hash'))
        assert signatures.setdefault(count, signature) == signature, (program, count)
        report['warmups' if repetition < 0 else 'runs'].append(row)
        print(json.dumps({'program': program, 'count': count, 'repetition': repetition,
                          'wall_seconds': row['wall_seconds']}), flush=True)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')

    for count in args.counts:
        for program in args.programs:
            record(program, count, -1)
        for repetition in range(args.repeats):
            k = repetition % len(args.programs)
            for program in args.programs[k:] + args.programs[:k]:
                record(program, count, repetition)

    aggregates = []
    for count in args.counts:
        for program in args.programs:
            rows = [r for r in report['runs'] if r['count'] == count and r['program'] == program]
            item = {'program': program, 'count': count, 'repetitions': len(rows)}
            for key in ('wall_seconds', 'generation_cpu_seconds'):
                values = [r[key] for r in rows]
                item[key + '_median'] = statistics.median(values)
                item[key + '_min'] = min(values)
                item[key + '_max'] = max(values)
            aggregates.append(item)
    report['aggregates'] = aggregates
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    with args.output.with_suffix('.csv').open('w', newline='') as target:
        writer = csv.DictWriter(target, fieldnames=list(aggregates[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(aggregates)


if __name__ == '__main__':
    main()
