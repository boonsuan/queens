#!/usr/bin/env python3
"""Generate the paper correspondence index from public Lean docstrings.

This is documentation tooling, not part of the proof. It rejects undocumented
named definitions and results; instances, fields, and auxiliary declarations
are outside the index.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
    r"(?:def|theorem|lemma|structure|inductive|abbrev)\s+([^\s({:]+)",
    re.MULTILINE,
)
DOCUMENTED = re.compile(
    r"/--(?P<doc>.*?)-/\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+)?(?:def|theorem|lemma|structure|inductive|abbrev)"
    r"\s+(?P<name>[^\s({:]+)",
    re.DOTALL,
)


def main():
    lines = [
        "# Declaration index",
        "",
        "Generated from the source docstrings by `python3 scripts/declaration_index.py`.",
        "The README maps modules to numbered paper results; the descriptions below",
        "record each named definition or result's role. Private helpers, instances,",
        "structure fields, and generated auxiliary declarations are omitted.",
        "",
    ]
    count = 0
    for path in sorted((ROOT / "Queens").rglob("*.lean")):
        source = path.read_text()
        documented = {m["name"]: m["doc"] for m in DOCUMENTED.finditer(source)}
        declarations = list(DECL.finditer(source))
        missing = [m[1] for m in declarations if m[1] not in documented]
        if missing:
            raise SystemExit(f"Undocumented declarations in {path}: {missing}")
        if not declarations:
            continue
        relative = path.relative_to(ROOT)
        lines += [f"## `{relative}`", "", "| Declaration | Purpose and paper correspondence |",
                  "|---|---|"]
        for decl in declarations:
            name = decl[1]
            line = source.count("\n", 0, decl.start()) + 1
            description = " ".join(documented[name].split())
            description = description.replace("|", "\\|")
            lines.append(f"| [`{name}`](../{relative}#L{line}) | {description} |")
            count += 1
        lines.append("")
    destination = ROOT / "docs" / "DECLARATIONS.md"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text("\n".join(lines))
    print(f"Indexed {count} documented public declarations in {destination.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
