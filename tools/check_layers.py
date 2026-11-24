#!/usr/bin/env python3
"""Check the dependency rules of the specification layers.

  Layer 1, spec/format: may import the Rocq standard library and Layer 1.
  Layer 2, spec/api:    may import the standard library and Layers 1 and 2.

Every import must be written `From <root> Require ...` so that it can be
checked.  The specification layers must also contain no axioms, parameters,
or admitted proofs.

Usage: tools/check_layers.py
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
RULES = {
    "spec/format": {"Stdlib", "fvzlib.format"},
    "spec/api": {"Stdlib", "fvzlib.format", "fvzlib.api"},
}
FORBIDDEN = re.compile(
    r"^\s*(?:Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|Variable|"
    r"Admitted|Abort)\b|\badmit\b")


def strip_comments(text):
    """Remove (possibly nested) Rocq comments."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            elif text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def main():
    errors, files = [], 0
    for directory, allowed in RULES.items():
        for path in sorted((ROOT / directory).glob("*.v")):
            files += 1
            rel = path.relative_to(ROOT)
            code = strip_comments(path.read_text())
            for n, line in enumerate(code.splitlines(), 1):
                if FORBIDDEN.search(line):
                    errors.append(f"{rel}:{n}: forbidden in a specification "
                                  f"layer: {line.strip()}")
                if not re.search(r"\bRequire\b", line):
                    continue
                m = re.match(r"\s*From\s+(\S+)\s+Require\b", line)
                if not m:
                    errors.append(f"{rel}:{n}: write imports as "
                                  f"`From <root> Require ...`")
                elif m.group(1) not in allowed:
                    errors.append(f"{rel}:{n}: {directory} may not import "
                                  f"from {m.group(1)}")
    print(f"layers: checked {files} file(s) in {len(RULES)} layer(s)")
    for e in errors:
        print(f"layers: ERROR {e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
