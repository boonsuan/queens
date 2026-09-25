#!/usr/bin/env python3
"""Check the recorded scan of Knuth's ranges without repeating it.

Reads results/knuth-bounds-1e11.json, its progress log and its environment
record, and checks with exact arithmetic that
  - the run completed, with one progress record every 10^9 queens;
  - in every record, the upper and lower counts plus the origin make up the
    count, and the reported extrema are attained by queens on the correct
    side of the diagonal, with the running extrema monotone;
  - the violation counts agree with the extrema (all are zero);
  - each printed deviation is within its stated error of the exact value
    s - c*phi or s - c/phi, recomputed to 70 digits;
  - the final row and checksum at 10^9 and 10^10 queens agree with the EC2
    benchmark runs (results/ec2-validation.json), made on another machine.

  python3 tests/check_bounds_results.py [--prefix results/knuth-bounds-1e11]
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(path):
    return json.loads(path.read_text(), parse_float=Decimal)


def sign(a, b):
    """Exact sign of a-b*sqrt(5), using Python arbitrary-precision integers."""
    if b == 0:
        return (a > 0) - (a < 0)
    if a >= 0 and b < 0:
        return 1
    if a <= 0 and b > 0:
        return -1
    difference = a*a - 5*b*b
    return ((difference > 0) - (difference < 0)) * (1 if a > 0 else -1)


def coefficient(witness, upper):
    return 2*witness["s"] + (-1 if upper else 1)*witness["c"]


def compare(left, right, upper):
    return sign(coefficient(left, upper) - coefficient(right, upper),
                left["c"] - right["c"])


def inside(witness, upper):
    lo, hi = (-2, 1) if upper else (-3, 5)
    a, c = coefficient(witness, upper), witness["c"]
    return sign(a-2*lo, c) >= 0 and sign(a-2*hi, c) <= 0


def check_witness(witness, upper, count):
    assert 1 <= witness["c"] <= count
    assert 0 < witness["s"] <= 2*count+1
    with localcontext() as context:
        context.prec = 70
        value = (Decimal(coefficient(witness, upper)) -
                 Decimal(witness["c"])*Decimal(5).sqrt())/2
        assert abs(value-witness["deviation"]) < witness["display_error_bound"]
        return format(value, ".18f")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", default="results/knuth-bounds-1e11")
    args = parser.parse_args()
    prefix = ROOT / args.prefix
    result_path = Path(str(prefix)+".json")
    progress_path = Path(str(prefix)+"-progress.log")
    environment = load(Path(str(prefix)+"-environment.json"))
    result = load(result_path)
    checkpoints = [json.loads(line, parse_float=Decimal)
                   for line in progress_path.read_text().splitlines() if line]
    assert environment["returncode"] == 0
    assert result["final"] and result["count"] == environment["count"]
    command = environment["command"]
    interval = int(command[command.index("--progress-every")+1])
    assert [record["count"] for record in checkpoints] == list(range(interval, result["count"], interval))
    assert all(not record["final"] for record in checkpoints)
    signatures = load(ROOT/"results/ec2-validation.json")["signatures"]
    matched_signatures = []
    previous = None
    extrema = {}
    for record in checkpoints + [result]:
        count = record["count"]
        assert count > 0 and (previous is None or count > previous["count"])
        assert record["last_column"] == count-1
        assert record["upper"]["count"] + record["lower"]["count"] + 1 == count
        assert record["origin_count"] == 1
        known = signatures.get(str(count))
        if known:
            assert all(record[key] == known[key] for key in ("last_column", "last_queen", "hash"))
            matched_signatures.append(count)
        for name, upper in (("upper", True), ("lower", False)):
            branch = record[name]
            if branch["count"] == 0:
                assert branch["minimum"] is None and branch["maximum"] is None
                continue
            for end in ("minimum", "maximum"):
                witness = branch[end]
                assert (witness["s"] > witness["c"]) if upper else (witness["s"] < witness["c"])
                extrema[name+"_"+end] = check_witness(witness, upper, count)
            assert compare(branch["minimum"], branch["maximum"], upper) <= 0
            both_inside = inside(branch["minimum"], upper) and inside(branch["maximum"], upper)
            assert (branch["branch_interval_violations"] == 0) == both_inside
            first = branch["first_branch_violation"]
            if branch["branch_interval_violations"]:
                assert first and not inside(first, upper)
                check_witness(first, upper, count)
            else:
                assert first is None
            if previous and previous[name]["count"]:
                assert compare(branch["minimum"], previous[name]["minimum"], upper) <= 0
                assert compare(branch["maximum"], previous[name]["maximum"], upper) >= 0
                assert branch["branch_interval_violations"] >= previous[name]["branch_interval_violations"]
        first = record["first_union_violation"]
        if record["union_violations"]:
            assert first and not inside(first, False) and not inside(first, True)
        else:
            assert first is None
        assert record["union_violations"] <= (record["upper"]["branch_interval_violations"] +
                                               record["lower"]["branch_interval_violations"])
        if previous:
            assert record["union_violations"] >= previous["union_violations"]
        previous = record
    summary = {
        "passed": True, "count": result["count"], "checkpoints": len(checkpoints),
        "matched_ec2_signature_counts": matched_signatures,
        "union_violations": result["union_violations"],
        "extrema_recomputed_to_18_decimal_places": extrema,
        "checks": ["completed run metadata", "column and branch counts",
                   "exact endpoint comparisons", "decimal rendering against 70-digit arithmetic",
                   "monotone running extrema", "EC2 prefix signatures"],
        "scope": "Consistency check of the recorded scan; does not repeat it",
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
