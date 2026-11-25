#!/usr/bin/env python3
"""Check the toolchain against the pinned versions, and report the target.

Run it inside the project's opam switch:

    opam exec --switch=fvzlib -- python3 tools/check_env.py

It checks two things.

  * Every package in env/packages.lock is installed at exactly that version,
    and the tools on the path come from that switch.
  * The machine and the installed CompCert are the project's first target,
    x86-64 Linux.  Anywhere else the proofs are exploratory, because the
    Clight they are about is generated for the local target.  The check
    fails there unless --exploratory is given.

It writes what it found to build/environment.txt.
"""
import argparse
import os
import pathlib
import platform
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LOCK = ROOT / "env" / "packages.lock"
# Written by env/Containerfile: what the toolchain image was built from.
PINS = pathlib.Path("/etc/fvzlib-toolchain")
TARGET = {"machine": "x86_64", "system": "Linux",
          "COMPCERT_ARCH": "x86", "COMPCERT_BITSIZE": "64",
          "COMPCERT_SYSTEM": "linux"}


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True)


def first_line(cmd):
    try:
        out = run(cmd)
    except FileNotFoundError:
        return "not found"
    text = (out.stdout or out.stderr).strip().splitlines()
    return text[0] if text else "no output"


def compcert_config(rocq_lib):
    path = rocq_lib / "user-contrib" / "compcert" / "compcert.config"
    values = {}
    if path.exists():
        for line in path.read_text().splitlines():
            if "=" in line and not line.startswith("#"):
                key, _, value = line.partition("=")
                values[key.strip()] = value.strip()
    return values


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--exploratory", action="store_true",
                    help="do not fail when this is not the project target")
    args = ap.parse_args()
    errors, report = [], []

    prefix = os.environ.get("OPAM_SWITCH_PREFIX")
    if not prefix:
        print("env: ERROR not inside an opam switch; run through "
              "`opam exec --switch=fvzlib --`")
        return 1
    prefix = pathlib.Path(prefix)
    report.append(f"opam switch: {prefix}")

    # ---- pinned versions ----
    wanted = dict(line.strip().split(".", 1)
                  for line in LOCK.read_text().splitlines() if line.strip())
    listed = run(["opam", "list", f"--switch={prefix.name}", "--short",
                  "--columns=name,version"])
    installed = dict(line.split() for line in listed.stdout.splitlines()
                     if len(line.split()) == 2)
    for name, version in sorted(wanted.items()):
        have = installed.get(name)
        if have != version:
            errors.append(f"{name}: want {version}, have {have or 'nothing'}")
    extra = sorted(n for n in installed
                   if n not in wanted and not n.startswith(("base-", "conf-")))
    for name in extra:
        errors.append(f"{name} {installed[name]}: installed but not in the "
                      f"lock file")
    report.append(f"packages: {len(wanted)} pinned, "
                  f"{len(wanted) - sum(1 for e in errors if 'want' in e)} match")

    # ---- the tools on the path come from the switch ----
    for tool in ("rocq", "clightgen", "ccomp"):
        found = shutil.which(tool)
        if not found:
            errors.append(f"{tool}: not on the path")
        elif prefix not in pathlib.Path(found).resolve().parents:
            errors.append(f"{tool}: found at {found}, outside the switch")
    report.append("rocq: " + first_line(["rocq", "--version"]))
    report.append("C compiler: " + first_line(["cc", "--version"]))
    report.append("python: " + platform.python_version())

    # ---- the container, when there is one ----
    image = os.environ.get("FVZLIB_IMAGE")
    if image:
        report.append(f"container image: {image}")
    if PINS.exists():
        report.extend(PINS.read_text().splitlines())

    # ---- the target ----
    where = run(["rocq", "-where"]).stdout.strip()
    config = compcert_config(pathlib.Path(where)) if where else {}
    found = {"machine": platform.machine(), "system": platform.system(),
             **{k: config.get(k, "unknown") for k in TARGET if k.startswith("COMPCERT")}}
    report.append(f"machine: {found['system']} {found['machine']}")
    report.append("CompCert target: {COMPCERT_ARCH}, {COMPCERT_BITSIZE} bits, "
                  "{COMPCERT_SYSTEM}".format(**found))
    on_target = found == TARGET
    if on_target:
        report.append("target: x86-64 Linux, the project's first target")
    else:
        report.append("target: NOT the project's first target, x86-64 Linux. "
                      "Results on this machine are exploratory.")
        if not args.exploratory:
            errors.append("this is not the project target; pass --exploratory "
                          "to check here anyway")

    (ROOT / "build").mkdir(exist_ok=True)
    (ROOT / "build" / "environment.txt").write_text("\n".join(report) + "\n")
    for line in report:
        print(f"env: {line}")
    for e in errors:
        print(f"env: ERROR {e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
