#!/usr/bin/env python3
"""Check that the proofs in a directory rest on allowed axioms only.

The directory holds a file AxiomAudit.v that prints, with
`Print Assumptions`, what each proven result depends on.  This script
compiles that file and requires that

  * every result is either closed, or depends only on axioms listed in
    audit/allowed-axioms.txt, each with the same statement as listed.  A
    result may also name a parameter of CompCert's semantics listed in
    audit/semantics-parameters.txt.  Those are not assumptions, and that
    file says why;
  * every lemma in the directory whose name starts with `body_`, which is
    how the proof of a C function's contract is named, is printed there.

An admitted lemma shows up as an axiom, so this also checks that nothing a
printed result depends on was admitted.

Usage: tools/check_axioms.py [--flags "ROCQ FLAGS"] DIRECTORY
       (run after the directory's Rocq sources are built)
"""
import argparse
import pathlib
import re
import shlex
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED = ROOT / "audit" / "allowed-axioms.txt"
PARAMETERS = ROOT / "audit" / "semantics-parameters.txt"
AUDIT = "AxiomAudit.v"
CLOSED = "Closed under the global context"
PRINT = re.compile(r"^\s*Print Assumptions\s+([\w.']+?)\s*\.\s*$", re.M)
BODY = re.compile(r"^\s*(?:Lemma|Theorem)\s+(body_[\w']*)", re.M)
ENTRY = re.compile(r"^([\w.']+)\s*:(.*)$")


def squash(text):
    """One axiom as `name : statement`, with all white space made single."""
    return " ".join(text.split())


def entries_of(path):
    """The entries of a list: blank-line separated, # for comments."""
    entries, current = set(), []
    for line in path.read_text().splitlines() + [""]:
        if line.startswith("#"):
            continue
        if line.strip():
            current.append(line)
        elif current:
            entries.add(squash(" ".join(current)))
            current = []
    return entries


def results(output):
    """What each `Print Assumptions` printed, in order.

    Returns (list, errors).  Each item is a list of axioms, empty for a
    closed result.  A line that cannot be understood is an error.
    """
    found, errors, block, entry = [], [], None, None

    def close_entry():
        nonlocal entry
        if entry is not None:
            block.append(squash(entry))
            entry = None

    for line in output.splitlines():
        if line.strip() == CLOSED:
            close_entry()
            block = None
            found.append([])
        elif line.strip() == "Axioms:":
            close_entry()
            block = []
            found.append(block)
        elif block is None:
            continue
        elif line[:1].isspace() and entry is not None:
            entry += " " + line
        elif line.startswith('File "') or not line.strip():
            close_entry()
            block = None
        elif ENTRY.match(line):
            close_entry()
            entry = line
        else:
            close_entry()
            errors.append(f"cannot read this line of an axiom list: {line}")
    close_entry()
    return found, errors


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("directory", type=pathlib.Path)
    ap.add_argument("--flags", default="",
                    help="the flags the directory's files are compiled with")
    args = ap.parse_args()
    here = args.directory.resolve()
    label = here.relative_to(ROOT) if ROOT in here.parents else here
    audit = here / AUDIT
    errors = []
    if not audit.exists():
        print(f"axioms: ERROR {label}: no {AUDIT}")
        return 1

    printed = PRINT.findall(audit.read_text())
    if not printed:
        errors.append(f"{AUDIT} prints nothing")
    short = {name.rsplit(".", 1)[-1] for name in printed}
    for path in sorted(here.glob("*.v")):
        if path.name == AUDIT:
            continue
        for lemma in BODY.findall(path.read_text()):
            if lemma not in short:
                errors.append(f"{path.name}: {lemma} is proven but {AUDIT} "
                              f"does not print its assumptions")

    with tempfile.TemporaryDirectory() as tmp:
        out = pathlib.Path(tmp) / "AxiomAudit.vo"
        run = subprocess.run(["rocq", "compile", *shlex.split(args.flags),
                              "-o", str(out), AUDIT],
                             cwd=here, capture_output=True, text=True)
    if run.returncode != 0:
        print(f"axioms: ERROR {label}: {AUDIT} does not compile")
        sys.stdout.write(run.stdout + run.stderr)
        return 1

    found, unread = results(run.stdout)
    errors += unread
    if len(found) != len(printed):
        errors.append(f"{len(printed)} results are printed in {AUDIT} but "
                      f"{len(found)} answers came back")
    allowed = entries_of(ALLOWED)
    parameters = entries_of(PARAMETERS)
    used = set()
    for name, axioms in zip(printed, found):
        for axiom in axioms:
            used.add(axiom)
            if axiom not in allowed and axiom not in parameters:
                errors.append(f"{name} depends on an axiom that is not in "
                              f"{ALLOWED.relative_to(ROOT)}:\n    {axiom}")

    # A result that only names parameters assumes nothing.
    closed = sum(1 for axioms in found if not set(axioms) - parameters)
    naming = sum(1 for axioms in found if set(axioms) & parameters)
    print(f"axioms: {label}: {len(found)} results, {closed} closed, "
          f"{len(found) - closed} resting on axioms; "
          f"{len(used & allowed)} of {len(allowed)} allowed axioms used"
          + (f"; {naming} name a parameter of CompCert's semantics"
             if naming else ""))
    for e in errors:
        print(f"axioms: ERROR {label}: {e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
