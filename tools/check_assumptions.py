#!/usr/bin/env python3
"""Check that the audited results depend on no axioms.

Compiles each file in audit/ and requires every `Print Assumptions` in it
to report "Closed under the global context".

Usage: tools/check_assumptions.py   (run after the Rocq sources are built)
"""
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
CLOSED = "Closed under the global context"


def main():
    flags = []
    for line in (ROOT / "_CoqProject").read_text().splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0] == "-Q":
            flags += ["-Q", str(ROOT / parts[1]), parts[2]]
    failed = False
    for path in sorted((ROOT / "audit").glob("*.v")):
        expected = len(re.findall(r"^\s*Print Assumptions\b", path.read_text(), re.M))
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp) / (path.stem + ".vo")
            run = subprocess.run(["rocq", "compile", *flags, "-o", str(out), str(path)],
                                 capture_output=True, text=True)
        closed = run.stdout.count(CLOSED)
        ok = run.returncode == 0 and closed == expected and expected > 0
        print(f"assumptions: {path.relative_to(ROOT)}: {closed} of {expected} "
              f"results are closed{'' if ok else '  ERROR'}")
        if not ok:
            failed = True
            sys.stdout.write(run.stdout + run.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
