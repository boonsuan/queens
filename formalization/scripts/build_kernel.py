#!/usr/bin/env python3
"""Build the large kernel certificates in stages to control peak memory.

This runs the ordinary Lake targets without changing their proof options. By
default the four largest independent parts are compiled sequentially. Passing
--parallel-forty lets Lake build those four parts together for a faster build
on machines with sufficient memory (roughly 10 GiB for the four Lean workers).
"""

import argparse
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def build(*targets: str) -> None:
    command = ["lake", "build", *targets]
    print("Running " + " ".join(command), flush=True)
    subprocess.run(command, cwd=ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--parallel-forty",
        action="store_true",
        help="compile the four largest parts together instead of sequentially",
    )
    args = parser.parse_args()

    # Build expensive prerequisites before targets that share them. This also
    # keeps independent large checks from competing for memory in a cold build.
    for module in (
        "Certificate",
        "SharpBounds",
        "StateCounts",
        "Reachability",
        "FortyHistoryChecks",
        "FortySeed",
    ):
        build(f"Queens.Finite.{module}")

    parts = [f"Queens.Finite.FortyStateChecksPart{i}" for i in range(4)]
    if args.parallel_forty:
        build(*parts)
    else:
        for part in parts:
            build(part)

    for module in ("FortyCertificate", "RunWitnesses", "RepeatedRunCertificate"):
        build(f"Queens.Finite.{module}")
    build()


if __name__ == "__main__":
    main()
