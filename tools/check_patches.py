#!/usr/bin/env python3
"""Apply and check the patch sequence.

This script:

  * exports the pinned upstream tree twice, into build/zlib-pristine and
    build/zlib-patched;
  * applies the patches named in patches/sequence, in order, to the second;
  * checks each patch header, and that its ledger entry exists;
  * marks the patched tree as altered, as the zlib license requires;
  * for each patch that names a witness, builds the witness against both
    trees and requires it to fail on the pristine one and pass on the
    patched one.

Usage: tools/check_patches.py [--upstream DIR] [--cc COMPILER]
"""
import argparse
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import io

ROOT = pathlib.Path(__file__).resolve().parent.parent
CLASSES = {"defect-fix", "hardening", "provability-fallback", "documentation"}
REQUIRED = ["Patch", "Subject", "Class", "Ledger", "C-editions-affected",
            "Applies-to", "Upstream-status"]
NEEDS_WITNESS = {"defect-fix", "hardening"}
LIBRARY = ["adler32", "compress", "crc32", "deflate", "gzclose", "gzlib",
           "gzread", "gzwrite", "infback", "inffast", "inflate", "inftrees",
           "trees", "uncompr", "zutil"]
# What the upstream configure script establishes on a POSIX system.
DEFINES = ["-DHAVE_UNISTD_H", "-DHAVE_STDARG_H"]
NOTICE = "FVZLIB-ALTERED.txt"


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def export(upstream, dest):
    """Export the tracked files of the upstream checkout into dest."""
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    archive = subprocess.run(["git", "-C", str(upstream), "archive", "HEAD"],
                             capture_output=True, check=True).stdout
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(dest, filter="data")


def header(path):
    """Parse the `Key: value` lines that open a patch file."""
    fields = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            break
        m = re.match(r"([A-Za-z-]+):\s*(.*)$", line)
        if m:
            fields[m.group(1)] = m.group(2).strip()
    return fields


def build_witness(cc, tree, witness, out):
    sources = [str(tree / (name + ".c")) for name in LIBRARY]
    return run([cc, "-O0", "-I", str(tree), *DEFINES, "-o", str(out),
                str(witness), *sources])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--upstream", default=str(ROOT / "upstream" / "zlib"))
    ap.add_argument("--cc", default="cc")
    args = ap.parse_args()

    upstream = pathlib.Path(args.upstream)
    errors = []
    if not (upstream / "zlib.h").exists():
        print(f"patches: ERROR no upstream tree at {upstream}")
        return 1
    commit = run(["git", "-C", str(upstream), "rev-parse", "HEAD"]).stdout.strip()

    build = ROOT / "build"
    pristine, patched = build / "zlib-pristine", build / "zlib-patched"
    export(upstream, pristine)
    export(upstream, patched)

    names = [line.strip()
             for line in (ROOT / "patches" / "sequence").read_text().splitlines()
             if line.strip() and not line.lstrip().startswith("#")]
    on_disk = sorted(p.name for p in (ROOT / "patches").glob("*.patch"))
    for extra in sorted(set(on_disk) - set(names)):
        errors.append(f"{extra}: in patches/ but not in the sequence")

    applied = []
    for name in names:
        path = ROOT / "patches" / name
        if not path.exists():
            errors.append(f"{name}: named in the sequence but missing")
            continue
        h = header(path)
        for key in REQUIRED:
            if not h.get(key):
                errors.append(f"{name}: header lacks {key}")
        if h.get("Patch") and h["Patch"] + ".patch" != name:
            errors.append(f"{name}: Patch field does not match the file name")
        cls = h.get("Class")
        if cls and cls not in CLASSES:
            errors.append(f"{name}: unknown class {cls}")
        ledger = h.get("Ledger")
        if ledger and not list((ROOT / "ledger").glob(ledger + "-*.md")):
            errors.append(f"{name}: no ledger entry {ledger}")
        if commit not in h.get("Applies-to", ""):
            errors.append(f"{name}: Applies-to does not name upstream "
                          f"commit {commit}")
        if cls in NEEDS_WITNESS and not h.get("Witness"):
            errors.append(f"{name}: class {cls} needs a witness")

        result = run(["patch", "-p1", "-s", "-d", str(patched), "-i", str(path)])
        if result.returncode != 0:
            errors.append(f"{name}: does not apply cleanly\n"
                          + result.stdout + result.stderr)
            continue
        for leftover in list(patched.rglob("*.orig")) + list(patched.rglob("*.rej")):
            leftover.unlink()
        applied.append((name, h))
        print(f"patches: applied {name} ({cls}, {ledger})")

    notice = ["This is an ALTERED version of zlib.  It is not the original software.",
              "",
              f"It was generated from upstream commit {commit}",
              "by applying the following patches, in order:",
              ""]
    notice += [f"  {name}  {h.get('Subject', '')}" for name, h in applied] or ["  (none)"]
    notice += ["", "The original software is available from https://zlib.net/.", ""]
    (patched / NOTICE).write_text("\n".join(notice))

    for name, h in applied:
        witness = h.get("Witness")
        if not witness:
            continue
        source = ROOT / witness
        if not source.exists():
            errors.append(f"{name}: witness {witness} not found")
            continue
        outcome = {}
        for label, tree in (("pristine", pristine), ("patched", patched)):
            exe = build / f"witness-{label}-{source.stem}"
            built = build_witness(args.cc, tree, source, exe)
            if built.returncode != 0:
                errors.append(f"{name}: witness does not build against the "
                              f"{label} tree\n{built.stderr}")
                break
            try:
                outcome[label] = subprocess.run([str(exe)], timeout=60).returncode
            except subprocess.TimeoutExpired:
                outcome[label] = "timeout"
        if len(outcome) == 2:
            print(f"patches: witness {source.name}: pristine exit "
                  f"{outcome['pristine']}, patched exit {outcome['patched']}")
            if outcome["pristine"] == 0:
                errors.append(f"{name}: witness passes on the pristine tree, "
                              f"so it does not demonstrate the finding here")
            if outcome["patched"] != 0:
                errors.append(f"{name}: witness fails on the patched tree")

    print(f"patches: {len(applied)} of {len(names)} applied to upstream "
          f"{commit[:12]}; patched tree in build/zlib-patched")
    for e in errors:
        print(f"patches: ERROR {e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
