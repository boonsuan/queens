"""Run every check for Section 6.5 and print a summary.

    python run_all.py          (from this directory)
    python oeis/run_all.py     (from the repository root)

In order: construct the forty-symbol history graph and explore both state
graphs (graphs.py); derive the run and gap bounds (runs_and_gaps.py), the
return words and faithful words (return_words.py), and the distances between
consecutive 4s (four_gaps.py); then check the occurrence witnesses in the
actual queens (witnesses.py). Any failed check stops the run with an error.
The results are written to results/. It takes about a minute.
"""
from __future__ import annotations

import sys
import time

import four_gaps
import graphs
import return_words
import runs_and_gaps
import witnesses

STEPS = [
    ('State graphs (graphs.py)', graphs.run),
    ('Column runs and gaps, upper bounds (runs_and_gaps.py)', runs_and_gaps.run),
    ('Return words to 3 (return_words.py)', return_words.run),
    ('Consecutive 4s (four_gaps.py)', four_gaps.run),
    ('Occurrence witnesses (witnesses.py)', witnesses.run),
]


def main() -> None:
    started = time.monotonic()
    for title, step in STEPS:
        print(title, flush=True)
        step_started = time.monotonic()
        try:
            lines = step()
        except graphs.CheckFailure as failure:
            print(f'  FAIL: {failure}')
            sys.exit(1)
        for line in lines:
            print('  PASS', line)
        print(f'  ({time.monotonic() - step_started:.0f} s)', flush=True)
    print(f'ALL CHECKS PASSED in {time.monotonic() - started:.0f} s; results in {graphs.RESULTS}')


if __name__ == '__main__':
    main()
