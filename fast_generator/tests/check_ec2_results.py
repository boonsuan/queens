#!/usr/bin/env python3
"""Check a benchmark campaign and recompute its summary (the timing table of Section 7.5).

By default this reads results/ec2-native.json, the EC2 campaign behind
the timing table, and checks that

  - it has one warmup and three timed runs of each program at each count,
    all pinned to the same CPU and built with the default flags;
  - every run exited normally, and its launcher statistics are consistent;
  - all runs at the same count report the same last row and checksum, and
    these agree with the values in KNOWN below;
  - the storage reported by each program is exact and the same in every run
    (the generator's fixed data are 34925 bytes; Knuth's packed arrays have
    the size given by his allocation rule);
  - the recorded medians, minima and maxima are those of the runs.

It prints the recomputed cells (medians and ranges of elapsed time, CPU time
and peak resident memory), the ratios of the median times, and the
signatures.  --environment compares the CPU, flags and launcher with a
separately captured machine record, such as results/ec2-environment.json.

  python3 tests/check_ec2_results.py --environment results/ec2-environment.json
  python3 tests/check_ec2_results.py results/new-benchmark.json --counts 1000000 10000000

The audit of the EC2 campaign is results/ec2-validation.json (written with
--output).
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import re
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = ("queens_fast", "knuth_packed")
FLAGS = "-O3 -std=c11 -DNDEBUG -fwrapv -Wall -Wextra -Wpedantic"

# The last row q_{N-1} and the checksum of q_0, ..., q_{N-1}, as printed by
# `build/queens_fast --count N` and `build/knuth_packed --count N`.  The
# values for 10^9 and 10^10 also appear in the scan of Knuth's ranges,
# results/knuth-bounds-1e11-progress.log, made on a different machine.
KNOWN = {
    1000: (617, "1e984fab2effb209"),
    10**6: (1618033, "a1eacbe1584dcd3c"),
    10**7: (16180339, "e90ab7b7e59e99ad"),
    10**8: (161803397, "ea78393604ed1025"),
    10**9: (1618033987, "264e17a4d3b5354d"),
    10**10: (16180339886, "fa45508ddb884185"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def number(value, name, *, positive=False, integer=False):
    require(isinstance(value, (int, float)) and not isinstance(value, bool),
            f"{name}: expected a number")
    require(math.isfinite(value) and (value > 0 if positive else value >= 0),
            f"{name}: expected a finite {'positive' if positive else 'nonnegative'} number")
    if integer:
        require(isinstance(value, int), f"{name}: expected an integer")
    return value


def summary_stats(values):
    return {"median": statistics.median(values), "min": min(values), "max": max(values)}


def knuth_array_bytes(n):
    """Bytes of Knuth's three occupancy arrays for n queens, one bit per flag.

    knuth/knuth_packed.c keeps Knuth's allocation rule: capacities
    floor(phi*n) + 10, that plus n, and n + 20 flags, each rounded up to
    whole 64-bit words.
    """
    max_a = int(1.6180339887498948482 * n) + 10
    capacities = (max_a, max_a + n, n + 20)
    return sum(8 * ((bits + 63) // 64) for bits in capacities)


def check_run(bucket, row, payloads):
    """Check one run; return its storage payload."""
    n, program, rep = row["count"], row["program"], row["repetition"]
    context = f"{bucket} {(n, program, rep)}"
    resource, summary = row["resources"], row["summary"]
    for field in ("wall_seconds", "driver_wall_seconds"):
        number(row[field], f"{context} {field}", positive=True)
    number(row["generation_cpu_seconds"], f"{context} generation CPU")
    require(resource["measurement_backend"] == "linux-native-wait4", f"{context}: unexpected launcher")
    require(resource["returncode"] == 0 and resource["timed_out"] is False,
            f"{context}: failed or timed out")
    require(resource["wall_seconds"] == row["wall_seconds"], f"{context}: inconsistent wall time")
    require(row["driver_wall_seconds"] >= row["wall_seconds"], f"{context}: driver time below launcher time")
    for field in ("cpu_seconds", "user_seconds", "system_seconds"):
        number(resource[field], f"{context} {field}")
    for field in ("peak_working_set_bytes", "page_faults", "minor_page_faults", "major_page_faults",
                  "voluntary_context_switches", "involuntary_context_switches"):
        number(resource[field], f"{context} {field}", integer=True)
    require(resource["page_faults"] == resource["minor_page_faults"] + resource["major_page_faults"],
            f"{context}: page-fault totals disagree")
    require(math.isclose(resource["cpu_seconds"], resource["user_seconds"] + resource["system_seconds"],
                         rel_tol=0, abs_tol=2e-9), f"{context}: CPU totals disagree")
    require(summary["seconds"] == row["generation_cpu_seconds"], f"{context}: CPU times disagree")
    require(summary["count"] == n and summary["last_column"] == n - 1, f"{context}: wrong count")
    number(summary["last_queen"], f"{context} last row", integer=True)
    require(isinstance(summary["hash"], str) and re.fullmatch(r"[0-9a-f]{16}", summary["hash"]),
            f"{context}: invalid checksum")
    if program == "queens_fast":
        require(summary["algorithm"] == "queens-fast-sparse-b4", f"{context}: unexpected generator")
        fields = ("levels", "generator_bytes", "producer_record_bytes", "symbol_buffer_bytes",
                  "heap_bytes", "static_data_bytes", "algorithm_bytes")
        for field in fields:
            number(summary[field], f"{context} {field}", positive=True, integer=True)
        require(summary["static_data_bytes"] == 34925, f"{context}: unexpected fixed data size")
        require(summary["heap_bytes"] == summary["generator_bytes"] +
                (summary["levels"] - 1) * summary["producer_record_bytes"] + summary["symbol_buffer_bytes"],
                f"{context}: heap accounting disagrees")
        require(summary["algorithm_bytes"] == summary["heap_bytes"] + summary["static_data_bytes"],
                f"{context}: storage accounting disagrees")
        for field in ("outer_macro_steps", "inner_macro_steps", "refill_calls"):
            require(summary[field] == 0, f"{context}: instrumented build")
    else:
        require(summary["algorithm"] == "knuth-packed", f"{context}: unexpected comparator")
        fields = ("requested_array_bytes", "algorithm_bytes")
        require(summary["requested_array_bytes"] == summary["algorithm_bytes"] == knuth_array_bytes(n),
                f"{context}: packed-array accounting disagrees")
    payload = {field: summary[field] for field in fields}
    require(payloads.setdefault((n, program), payload) == payload,
            f"{context}: storage differs between runs")
    return (n, n - 1, summary["last_queen"], summary["hash"])


def validate(data, counts, captured=None):
    arguments, environment = data["arguments"], data["environment"]
    require(arguments["counts"] == counts, "campaign counts differ from the requested counts")
    require(arguments["programs"] == list(PROGRAMS), "unexpected programs or program order")
    require(arguments["repeats"] == 3, "expected three timed repetitions")
    cpu = number(arguments["cpu"], "cpu", integer=True)
    require(environment["pinned_cpu"] == cpu and environment["cpu_affinity"] == [cpu],
            "CPU affinity and recorded configuration disagree")
    require(environment["flags"] == FLAGS, "unexpected compiler flags")
    if captured is not None:
        require(captured["cpu"] == cpu, "separately captured CPU disagrees")
        for key in ("flags", "measurement_backend"):
            require(captured[key] == environment[key], f"separately captured {key} disagrees")

    signatures, payloads, rows_by_cell, warnings = {}, {}, {}, []
    for bucket, repetitions in (("warmups", {-1}), ("runs", {0, 1, 2})):
        expected_keys = {(n, p, r) for n in counts for p in PROGRAMS for r in repetitions}
        seen = set()
        for row in data[bucket]:
            key = (row["count"], row["program"], row["repetition"])
            require(key in expected_keys and key not in seen, f"unexpected or duplicate {bucket} run {key}")
            seen.add(key)
            signature = check_run(bucket, row, payloads)
            n = row["count"]
            require(signatures.setdefault(n, signature) == signature, f"{key}: signatures disagree")
            if n in KNOWN:
                require(signature[2:] == KNOWN[n], f"{key}: signature differs from KNOWN")
            if bucket == "runs":
                rows_by_cell.setdefault((n, row["program"]), []).append(row)
            if row["resources"]["major_page_faults"]:
                warnings.append(f"{key}: {row['resources']['major_page_faults']} major page faults")
        require(seen == expected_keys, f"{bucket}: missing runs {sorted(expected_keys - seen)}")

    cells = []
    for aggregate in data["aggregates"]:
        key = (aggregate["count"], aggregate["program"])
        rows = rows_by_cell[key]
        require(aggregate["repetitions"] == len(rows) == 3, f"aggregate {key}: wrong repetition count")
        cell = {"count": key[0], "program": key[1], "repetitions": 3, "storage": payloads[key]}
        for field in ("wall_seconds", "generation_cpu_seconds"):
            stats = summary_stats([r[field] for r in rows])
            for statistic, value in stats.items():
                require(aggregate[field + "_" + statistic] == value,
                        f"aggregate {key}: incorrect {field} {statistic}")
            cell[field] = stats
        for field in ("peak_working_set_bytes", "cpu_seconds", "major_page_faults"):
            cell[field] = summary_stats([r["resources"][field] for r in rows])
        cells.append(cell)
    require(sorted((c["count"], c["program"]) for c in cells) == sorted(rows_by_cell),
            "missing or duplicate aggregate cells")
    by_key = {(cell["count"], cell["program"]): cell for cell in cells}
    ratios = [{"count": n, "packed_over_fast_wall_median":
               by_key[n, "knuth_packed"]["wall_seconds"]["median"] /
               by_key[n, "queens_fast"]["wall_seconds"]["median"]} for n in counts]
    return {"passed": True, "counts": counts, "cpu": cpu, "warmup_runs": len(data["warmups"]),
            "timed_runs": len(data["runs"]), "aggregate_cells": len(cells),
            "checked_against_environment_record": captured is not None,
            "signatures": {str(n): {"last_column": n - 1, "last_queen": signatures[n][2],
                                    "hash": signatures[n][3]} for n in counts},
            "cells": cells, "speedup_ratios": ratios, "warnings": warnings}


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("input", nargs="?", type=Path, default=ROOT / "results" / "ec2-native.json")
    parser.add_argument("--counts", nargs="+", type=int, default=[10**n for n in range(6, 11)])
    parser.add_argument("--environment", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        captured = (json.loads(args.environment.read_text(encoding="utf-8"))
                    if args.environment else None)
        report = validate(data, args.counts, captured)
        rendered = json.dumps(report, indent=2, allow_nan=False) + "\n"
        if args.output:
            require(args.output.resolve() != args.input.resolve(), "the output must not overwrite the input")
            with open(args.output, "w", encoding="utf-8", newline="\n") as output:
                output.write(rendered)
        print(rendered, end="")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Benchmark check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
