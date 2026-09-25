"""Shared deterministic rendering for untrusted Lean certificate inputs.

The balanced layout and bounded proof partitions are evaluation optimizations,
not mathematical assumptions. Every generated check is verified by Lean.
"""
from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path
import re


def scope_heartbeats(text: str) -> str:
    """Scope a generated module's evaluation budget to each theorem.

    The generated declarations are all finite checks or their assemblies.
    Mathematical handwritten modules choose their budgets independently.
    """
    budget = re.search(r"^set_option maxHeartbeats (\d+)\n", text, re.MULTILINE)
    if budget is None:
        return text
    text = text[:budget.start()] + text[budget.end():]
    lines = text.splitlines()
    starts = []
    for i, line in enumerate(lines):
        if not re.match(r"(?:private )?theorem ", line):
            continue
        start = i
        if i and lines[i - 1].endswith("-/"):
            while start and not lines[start].startswith("/--"):
                start -= 1
        starts.append(start)
    for start in reversed(starts):
        lines[start:start] = [f"set_option maxHeartbeats {budget[1]} in",
                             "-- This finite certificate is reduced by the Lean kernel."]
    return "\n".join(lines) + "\n"


def write_lean(path: Path, text: str) -> None:
    """Write deterministic Lean source with narrow generated-layout exceptions.

    Large literals and bounded proof partitions are intentionally retained:
    changing their shape can greatly increase kernel reduction memory.
    """
    text = scope_heartbeats(text)
    options = []
    if any(len(line) > 100 for line in text.splitlines()):
        options += ["-- Generated tree literals and check statements preserve the evaluation layout.",
                    "set_option linter.style.longLine false"]
    if len(text.splitlines()) > 1500:
        # Allow exactly the lint-recommended rounded bound, including these options.
        bound = (len(text.splitlines()) + len(options) + 3) // 100 * 100 + 200
        options += ["-- The complete generated certificate is kept in deterministic traversal order.",
                    f"set_option linter.style.longFile {bound}"]
    if options:
        position = text.index("namespace ")
        text = text[:position] + "\n".join(options) + "\n\n" + text[position:]
    path.write_text(text, encoding="utf-8")


def balanced_tree(
    entries: Sequence[str], entry_type: str, prefix: str, chunk_size: int = 64
) -> tuple[list[str], str]:
    """Render an in-order tree, naming leaves of at most ``chunk_size`` nodes.

    Callers render individual payloads; this helper alone chooses the tree
    shape. The split convention must agree with ``indexed_checks`` below.
    """
    if chunk_size < 1:
        raise ValueError("tree chunks must contain at least one node")
    lines: list[str] = []
    serial = 0

    def literal(items: Sequence[str]) -> str:
        if not items:
            return ".nil"
        middle = len(items) // 2
        return (f"(.node {items[middle]} {literal(items[:middle])} "
                f"{literal(items[middle + 1:])})")

    def render(items: Sequence[str]) -> str:
        nonlocal serial
        if len(items) <= chunk_size:
            name = f"{prefix}{serial}"
            serial += 1
            lines.extend([f"private def {name} : BinaryTree {entry_type} :=",
                          "  " + literal(items), ""])
            return name
        middle = len(items) // 2
        left = render(items[:middle])
        right = render(items[middle + 1:])
        return f"(.node {items[middle]} {left} {right})"

    root = render(entries)
    return lines, root


def indexed_checks(
    lines: list[str], count: int, path: str, predicate: str, prefix: str,
    chunk_size: int = 64,
) -> str:
    """Append bounded kernel checks and return their assembled theorem name.

    Each branch checks its root as well as both children. Opaque intermediate
    theorems bound the kernel reduction cache without omitting any entry.
    """
    if count < 0 or chunk_size < 1:
        raise ValueError("invalid tree size or proof chunk size")
    serial = 0

    def emit(size: int, subtree: str) -> str:
        nonlocal serial
        left = right = None
        if size > chunk_size:
            middle = size // 2
            left = emit(middle, subtree + ".left")
            right = emit(size - middle - 1, subtree + ".right")
        name = f"{prefix}{serial}"
        serial += 1
        lines.extend([f"private theorem {name} :",
                      f"    indexedAll {predicate} ({subtree}) = true := by"])
        if left is None:
            lines.append("  decide +kernel")
        else:
            lines.extend(["  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr",
                          f"    ⟨by decide +kernel, {left}⟩, {right}⟩"])
        lines.append("")
        return name

    return emit(count, path)
