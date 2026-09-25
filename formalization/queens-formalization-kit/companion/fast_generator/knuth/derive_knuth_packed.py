#!/usr/bin/env python3
"""Derive knuth_packed.c, the comparator of the timing table, from Knuth's infty-queens.

Donald Knuth's CWEB program infty-queens.w computes the greedy-queen rows
with three occupancy arrays a, b, c of one byte per flag.  This script
builds a generation-and-checksum program from it:

  1. CTANGLE infty-queens.w, and take from the resulting C the array
     allocation (section 3 of the CWEB program) and the placement of one
     queen (section 4), verbatim, with their #line directives.
  2. Remove the tick-counter reset from section 4 and define Knuth's
     tick-counting macro `o` to do nothing.
  3. Store the three arrays as bits in 64-bit words: replace the three
     callocs, the six writes `x[i]= 1;` by SET(x, i) and the five reads
     x[i] by GET(x, i), and widen the counts and indices to int64_t.  The
     placement order and control flow are Knuth's; assertion builds
     check every index.
  4. Wrap them in the command line of queens_fast: `--count N [--emit]`,
     zero-based rows (Knuth's are one-based), the same checksum of all
     rows, and a JSON summary with the requested array bytes.  Knuth's
     per-queen printing, statistics and Fibonacci bookkeeping are omitted.

  python3 knuth/derive_knuth_packed.py --check      # compare with knuth_packed.c
  python3 knuth/derive_knuth_packed.py --source infty-queens.w --output out.c

Without --source the CWEB file is downloaded from Knuth's web page.  The
ctangle program (from TeX Live or the CWEB distribution) must be on the
PATH, or given with --ctangle.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import urllib.request

URL = "https://www-cs-faculty.stanford.edu/~knuth/programs/infty-queens.w"
HERE = Path(__file__).resolve().parent

PREAMBLE = r'''/* Derived by knuth/derive_knuth_packed.py from Knuth's infty-queens.w:
 * its array allocation and queen placement, with the occupancy flags stored
 * as bits in 64-bit words and 64-bit counts and indices, in a program that
 * generates and checksums the rows like build/queens_fast.
 */
#include <assert.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define slack 10
#define phi 1.6180339887498948482
#define o ((void)0)
int64_t goal;
uint64_t *a, *b, *c;
int64_t maxmema, maxmemb, minmemc, maxmemc;
uint64_t a_bits, b_bits, c_bits;

/* Each occupancy flag occupies one bit in a 64-bit unsigned word. */
static uint64_t packed_bytes(uint64_t bits) {
    return ((bits + 63) / 64) * sizeof(uint64_t);
}
static unsigned get_bit(const uint64_t *bits, uint64_t index) {
    return (unsigned)((bits[index >> 6] >> (index & 63)) & UINT64_C(1));
}
static void set_bit(uint64_t *bits, uint64_t index) {
    bits[index >> 6] |= UINT64_C(1) << (index & 63);
}
/* The assert-enabled build also checks the reads, which Knuth leaves unchecked. */
#define GET(array, index) \
    (assert((index) >= 0 && (uint64_t)(index) < array##_bits), \
     get_bit(array, (uint64_t)(index)))
#define SET(array, index) \
    (assert((index) >= 0 && (uint64_t)(index) < array##_bits), \
     set_bit(array, (uint64_t)(index)))


int main(int argc, char **argv) {
    int emit = 0;
    uint64_t count = 0, hash = UINT64_C(14695981039346656037);
    uint64_t computed = 0, last_row = 0;
    int64_t k, n, q, r, s, t;
    clock_t started;
    for (int arg = 1; arg < argc; ++arg) {
        if (!strcmp(argv[arg], "--emit")) emit = 1;
        else if (!strcmp(argv[arg], "--count") && arg + 1 < argc) {
            char *end;
            errno = 0;
            const char *value = argv[++arg];
            if (*value == '-') return 2;
            count = strtoull(value, &end, 10);
            if (errno || *end || end == value) return 2;
        } else {
            fprintf(stderr, "Usage: %s --count N [--emit]\n", argv[0]);
            return 2;
        }
    }
    /* Limit this adapter to its intended benchmark range. All placement
       arithmetic and allocation sizes use 64-bit types; signed indices
       are needed for k-n and Knuth's diagonal-offset tests. */
    if (sizeof(size_t) < 8 || !count || count > UINT64_C(1000000000000)) {
        fprintf(stderr, "requires 64-bit size_t and count in [1, 1000000000000]\n");
        return 2;
    }
    goal = (int64_t)count;
    started = clock();
'''

LOOP_START = r'''
    r = t = 0; s = 1;
    for (n = 1; n <= goal; ++n) {
'''

EPILOGUE = r'''
        ; /* The extracted chunk ends with label got_q. */
        last_row = (uint64_t)(q - 1);
        hash = (hash ^ last_row) * UINT64_C(1099511628211);
        ++computed;
        if (emit) printf("%" PRId64 " %" PRIu64 "\n", n - 1, last_row);
    }
done:
    {
        double seconds = (double)(clock() - started) / CLOCKS_PER_SEC;
        uint64_t bytes = packed_bytes(a_bits) + packed_bytes(b_bits)
                       + packed_bytes(c_bits);
        FILE *summary = emit ? stderr : stdout;
        if (computed != count) {
            fprintf(stderr, "Knuth allocation was exhausted after %" PRIu64
                    " queens (requested %" PRIu64 ")\n", computed, count);
            free(a); free(b); free(c);
            return 3;
        }
        fprintf(summary,
                "{\"algorithm\":\"knuth-packed\",\"count\":%" PRIu64 ",\"last_column\":%" PRIu64
                ",\"last_queen\":%" PRIu64 ",\"hash\":\"%016" PRIx64
                "\",\"requested_array_bytes\":%" PRIu64
                ",\"algorithm_bytes\":%" PRIu64 ",\"seconds\":%.9f}\n",
                count, count - 1, last_row, hash, bytes, bytes, seconds);
        free(a); free(b); free(c);
    }
    return 0;
}
'''


def replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"expected exactly one occurrence of {old!r}")
    return text.replace(old, new)


def chunk(tangled: str, number: int) -> str:
    """The C code of CWEB section `number`, between /*n:*/ and /*:n*/."""
    matches = re.findall(rf"/\*{number}:\*/(.*?)/\*:{number}\*/", tangled, flags=re.DOTALL)
    if len(matches) != 1:
        raise ValueError(f"expected exactly one tangled section {number}")
    return matches[0]


def derive(tangled: str) -> str:
    allocation, placement = chunk(tangled, 3), chunk(tangled, 4)

    # Step 2: no tick counting.
    for expected in ("for(k= s;k<=n-r;k++)", "q= n+t;", "got_q:"):
        if expected not in placement:
            raise ValueError(f"expected placement operation {expected!r}")
    placement = replace_once(placement, "ticks= 0;\n", "")

    # Step 3: 64-bit sizes and bit-packed arrays.
    allocation = replace_once(allocation, "maxmema= ((int)(phi*goal)+slack);",
                              "maxmema= ((int64_t)(phi*goal)+slack);")
    for name, capacity in (("a", "maxmema"), ("b", "maxmemb"), ("c", "minmemc+maxmemc")):
        allocation = replace_once(
            allocation, f"{name}= (char*)calloc({capacity},sizeof(char));",
            f"{name}_bits= (uint64_t)({capacity});\n"
            f"{name}= (uint64_t*)calloc((size_t)(({name}_bits+63)/64),sizeof(uint64_t));")
    placement, writes = re.subn(r"([abc])\[([^\]\n]+)\]= 1;", r"SET(\1, \2);", placement)
    placement, reads = re.subn(r"([abc])\[([^\]\n]+)\]", r"GET(\1, \2)", placement)
    if (writes, reads) != (6, 5):
        raise ValueError(f"expected six writes and five reads, found {writes} and {reads}")

    # Step 4: the program around them.
    return PREAMBLE + allocation + LOOP_START + placement + EPILOGUE


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source", type=Path, help="a local copy of infty-queens.w")
    parser.add_argument("--ctangle", default=shutil.which("ctangle"))
    parser.add_argument("--output", type=Path, default=HERE / "knuth_packed.c")
    parser.add_argument("--check", action="store_true",
                        help="compare with --output instead of writing it")
    args = parser.parse_args()
    if not args.ctangle:
        parser.error("ctangle not found; pass --ctangle PATH")
    if args.source:
        web = args.source.read_bytes()
    else:
        with urllib.request.urlopen(URL, timeout=60) as response:
            web = response.read()
    with tempfile.TemporaryDirectory() as directory:
        (Path(directory) / "infty-queens.w").write_bytes(web)
        subprocess.run([args.ctangle, "infty-queens.w"], cwd=directory, check=True,
                       capture_output=True)
        tangled = (Path(directory) / "infty-queens.c").read_text(encoding="utf-8")
    derived = derive(tangled)
    if args.check:
        if args.output.read_text(encoding="utf-8") != derived:
            raise SystemExit(f"{args.output} differs from the derived program")
        print(f"{args.output} matches the program derived from infty-queens.w")
    else:
        with open(args.output, "w", encoding="utf-8", newline="\n") as output:
            output.write(derived)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
