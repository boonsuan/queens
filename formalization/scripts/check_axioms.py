#!/usr/bin/env python3
"""Run Lean's project-wide axiom audit and reject any extra trust.

This script does not establish mathematical facts. Lean computes the actual
axiom dependencies of all imported project declarations; this script makes
the project's kernel-only requirement an explicit, repeatable check.
"""

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    audit = ROOT / "AxiomAudit.lean"
    expected = re.findall(r"^#print axioms (\S+)\s*$", audit.read_text(), re.MULTILINE)
    result = subprocess.run(
        ["lake", "env", "lean", str(audit)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise SystemExit(result.returncode)

    reports = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
        result.stdout,
        re.DOTALL,
    )
    actual = {name for name, _ in reports}
    if actual != set(expected):
        raise SystemExit(
            f"Unexpected audit coverage: missing={set(expected) - actual}, "
            f"extra={actual - set(expected)}\n{result.stdout}"
        )
    for name, axioms in reports:
        dependencies = {item.strip() for item in axioms.split(",") if item.strip()}
        extra = dependencies - ALLOWED
        if extra:
            raise SystemExit(f"{name} has disallowed axiom dependencies: {sorted(extra)}")

    project_report = re.search(
        r"Kernel-only audit passed for all ([0-9]+) imported project declarations\.",
        result.stdout,
    )
    if project_report is None or int(project_report[1]) == 0:
        raise SystemExit(f"Missing project-wide audit result:\n{result.stdout}")

    output = ROOT / "docs" / "AXIOMS.txt"
    output.write_text(result.stdout)
    print(
        f"Kernel-only axiom audit passed for all {project_report[1]} project declarations "
        f"and {len(expected)} named principal results."
    )
    print("Allowed foundations: propext, Classical.choice, Quot.sound.")


if __name__ == "__main__":
    main()
