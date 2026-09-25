#!/usr/bin/env python3
"""Run the scan of Knuth's ranges and record its result and environment.

build/scan_bounds checks, for the one-based coordinates c = n + 1 and
s(c) = q_n + 1 with 1 <= c <= COUNT, that every queen lies in
[c/phi - 3, c/phi + 5] or [c*phi - 2, c*phi + 1], and records the extreme
deviations (see the remark on 1-indexed coordinates in Section 3).  This
script runs it and writes three files:

  PREFIX.json               the scanner's final JSON record
  PREFIX-progress.log       one JSON record every --progress-every queens
  PREFIX-environment.json   machine, compiler, command and elapsed time

  make build/scan_bounds
  python3 bench/run_bounds_scan.py --count 100000000000 --prefix results/my-scan

The recorded scan is results/knuth-bounds-1e11*.  Linux only (it reads
/etc/os-release and /proc).
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--count", type=int, default=10**11)
    parser.add_argument("--progress-every", type=int, default=10**9)
    parser.add_argument("--prefix", default="results/new-knuth-bounds")
    parser.add_argument("--compiler", default="cc",
                        help="compiler whose --version is recorded")
    parser.add_argument("--flags", default="-O3 -std=c11 -DNDEBUG -fwrapv -Wall -Wextra -Wpedantic",
                        help="build flags to record (make's default)")
    args = parser.parse_args()
    if not 1 <= args.count <= 10**11 or args.progress_every < 1:
        parser.error("count must be in [1, 10^11] and the progress interval positive")

    prefix = ROOT / args.prefix
    paths = {"result": Path(str(prefix) + ".json"),
             "progress": Path(str(prefix) + "-progress.log"),
             "environment": Path(str(prefix) + "-environment.json")}
    if any(path.exists() for path in paths.values()):
        parser.error("an output file already exists; choose a new --prefix")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    command = ["build/scan_bounds", "--count", str(args.count),
               "--progress-every", str(args.progress_every)]
    metadata = {
        "purpose": "Finite check of Knuth's ranges, separate from the EC2 speed comparison",
        "started_utc": utc_now(), "count": args.count,
        "coordinate_convention": "c = n + 1; s(c) = q_n + 1; count includes the origin",
        "command": command,
        "platform": platform.platform(), "python": platform.python_version(),
        "logical_cpus": os.cpu_count(), "cpu_affinity": "not pinned",
        "compiler": subprocess.check_output([args.compiler, "--version"], text=True),
        "reported_build_flags": args.flags,
        "outputs": {key: os.path.relpath(path, ROOT) for key, path in paths.items()},
    }
    for name, path in (("os_release", "/etc/os-release"),
                       ("cpuinfo", "/proc/cpuinfo"),
                       ("meminfo", "/proc/meminfo")):
        if Path(path).exists():
            metadata[name] = Path(path).read_text()

    def save_metadata() -> None:
        paths["environment"].write_text(json.dumps(metadata, indent=2) + "\n")

    save_metadata()
    print(f"Scanning {args.count} queens; progress: {paths['progress']}", flush=True)
    started = time.perf_counter()
    with paths["result"].open("w") as output, paths["progress"].open("w") as progress:
        run = subprocess.run(command, cwd=ROOT, stdout=output, stderr=progress)
    metadata.update(finished_utc=utc_now(), returncode=run.returncode,
                    wall_seconds=time.perf_counter() - started)
    save_metadata()
    if run.returncode:
        raise SystemExit("The scan failed; see the progress log")
    result = json.loads(paths["result"].read_text())
    if result["count"] != args.count:
        raise SystemExit("The scanner reported the wrong count")
    print(f"Completed in {metadata['wall_seconds']:.3f} s; result: {paths['result']}")


if __name__ == "__main__":
    main()
