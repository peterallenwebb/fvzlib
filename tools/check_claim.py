#!/usr/bin/env python3
"""Check what the claims in claims/*.toml refer to.

A claim is prose, in claims/NAME.md.  Beside it, claims/NAME.toml lists
what the prose refers to in the repository.  For each such list this
checks that:

  * the commit is the one the upstream submodule is pinned to;
  * the patches are the patch sequence, in order;
  * the flags are those in proofs/zlib.mk;
  * each toolchain package is pinned in env/packages.lock;
  * the theorem exists, and its assumptions are printed in the audit file
    that tools/check_axioms.py checks;
  * the axioms are exactly those in audit/allowed-axioms.txt;
  * the functions are exactly those the translated source file defines,
    each with a known state, a patch from the sequence if it needs one,
    and a contract that is in the theorem's list;
  * every entry of the ledger is listed with a role, an entry the claim
    relies on is still unproven, and a finding is still a finding;
  * the prose names the commit, each patch, each flag, each version, the
    theorem, each axiom, each function, each contract, and each ledger
    entry.

It reads text only.  It does not judge the wording of a claim.  What it
guarantees is that the things a claim names exist and are the ones the
build uses.  Run it after the proofs are built.

Usage: tools/check_claim.py [--upstream DIR]
"""
import argparse
import pathlib
import re
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
STATES = {"proven as is", "proven after a patch"}
ROLES = {"finding", "relied on", "not relied on"}


def strip_comments(text):
    """Remove Rocq comments, which may nest."""
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
            i += 1
    return "".join(out)


def uncommented(path):
    return [line.strip() for line in path.read_text().splitlines()
            if line.strip() and not line.startswith("#")]


def axiom_names():
    """The names in audit/allowed-axioms.txt: the word before each colon
    that starts an entry."""
    names, fresh = [], True
    for line in (ROOT / "audit" / "allowed-axioms.txt").read_text().splitlines():
        if line.startswith("#"):
            continue
        if not line.strip():
            fresh = True
        elif fresh:
            names.append(line.split(":")[0].strip())
            fresh = False
    return names


def ledger_status(path):
    match = re.search(r"^\|\s*Status\s*\|(.*)\|\s*$", path.read_text(), re.M)
    return match.group(1).strip() if match else ""


def check(path, upstream):
    ref = tomllib.loads(path.read_text())
    errors = []

    def need(ok, message):
        if not ok:
            errors.append(message)

    prose_path = ROOT / ref["claim"]
    prose = " ".join(prose_path.read_text().split()) if prose_path.exists() else ""
    need(prose, f"{ref['claim']}: no such file")

    def named(what, text):
        need(text in prose, f"{ref['claim']} does not name {what} {text}")

    # ---- the subject ----
    subject = ref["subject"]
    pinned = subprocess.run(["git", "-C", str(upstream), "rev-parse", "HEAD"],
                            capture_output=True, text=True).stdout.strip()
    need(subject["commit"] == pinned,
         f"commit {subject['commit']} is not the pinned one, {pinned}")
    named("the commit", subject["commit"])
    sequence = uncommented(ROOT / "patches" / "sequence")
    need(subject["patches"] == sequence,
         f"patches {subject['patches']} are not the sequence {sequence}")
    for patch in subject["patches"]:
        named("the patch", patch)

    # ---- the configuration and the toolchain ----
    mk = (ROOT / "proofs" / "zlib.mk").read_text()
    defines = re.search(r"^ZLIB_DEFINES\s*:=\s*(.*)$", mk, re.M).group(1).strip()
    need(ref["configuration"]["defines"] == defines,
         f"flags are not those of proofs/zlib.mk: {defines}")
    for flag in ref["configuration"]["defines"].split():
        named("the flag", flag)
    named("the target", ref["configuration"]["target"])
    lock = set(uncommented(ROOT / "env" / "packages.lock"))
    for package in ref["toolchain"]["packages"]:
        need(package in lock, f"{package} is not pinned in env/packages.lock")
        named("the version", package.split(".", 1)[1])

    # ---- the theorem ----
    theorem = ref["theorem"]
    file = ROOT / theorem["file"]
    text = strip_comments(file.read_text()) if file.exists() else ""
    need(re.search(r"^Theorem\s+%s\b" % re.escape(theorem["name"]), text, re.M),
         f"no theorem {theorem['name']} in {theorem['file']}")
    audit = strip_comments((ROOT / theorem["audit"]).read_text())
    need(re.search(r"^Print Assumptions\s+%s\.%s\." % (file.stem, theorem["name"]),
                   audit, re.M),
         f"{theorem['audit']} does not print the assumptions of "
         f"{file.stem}.{theorem['name']}")
    named("the theorem", theorem["name"])
    need(sorted(theorem["axioms"]) == sorted(axiom_names()),
         "the axioms are not those of audit/allowed-axioms.txt")
    for axiom in theorem["axioms"]:
        named("the axiom", axiom)
    listed = re.search(r"^Definition\s+%s\b[^:]*:[^:]*:=(.*?)\.\s" % theorem["contracts"],
                       text, re.M | re.S)
    contracts = set(re.findall(r"\w+", listed.group(1))) if listed else set()
    need(listed, f"no list {theorem['contracts']} in {theorem['file']}")

    # ---- the functions ----
    clight = file.parent / (pathlib.Path(subject["source"]).stem + "_clight.v")
    if clight.exists():
        defined = re.findall(r"^Definition f_(\w+) :=", clight.read_text(), re.M)
    else:
        defined = None
        errors.append(f"{clight.relative_to(ROOT)} is missing; build the proofs first")
    functions = ref.get("function", [])
    if defined is not None:
        need(sorted(f["name"] for f in functions) == sorted(defined),
             f"functions listed are not those the file defines: {sorted(defined)}")
    need(len(contracts) == len(functions),
         f"{theorem['contracts']} has {len(contracts)} contracts for "
         f"{len(functions)} functions")
    for function in functions:
        name = function["name"]
        need(function.get("state") in STATES, f"{name}: unknown state")
        if function.get("state") == "proven after a patch":
            need(function.get("patch") in sequence,
                 f"{name}: its patch is not in the sequence")
        else:
            need("patch" not in function, f"{name}: proven as is, but names a patch")
        need(function.get("contract") in contracts,
             f"{name}: contract {function.get('contract')} is not in "
             f"{theorem['contracts']}")
        named("the function", f"`{name}`")
        named("the contract", function.get("contract", "?"))

    # ---- the ledger ----
    entries = {p.name.split("-")[0]: p for p in sorted((ROOT / "ledger").glob("*.md"))}
    roles = {e["entry"]: e for e in ref.get("ledger", [])}
    for entry in sorted(set(entries) - set(roles)):
        errors.append(f"ledger entry {entry} is not listed")
    for entry, item in roles.items():
        if entry not in entries:
            errors.append(f"{entry}: no such ledger entry")
            continue
        need(item.get("role") in ROLES, f"{entry}: unknown role")
        need(item.get("note", "").strip(), f"{entry}: no note")
        status = ledger_status(entries[entry])
        if item.get("role") == "relied on":
            need("unproven" in status.lower(),
                 f"{entry}: relied on as unproven, but its status is: {status}")
        if item.get("role") == "finding":
            need(entry.startswith("F"), f"{entry}: not a finding")
        named("the ledger entry", entry)

    shown = path.relative_to(ROOT)
    relied = sorted(e for e, i in roles.items() if i.get("role") == "relied on")
    print(f"claim: {shown}: {subject['release']} at {subject['commit'][:12]}, "
          f"{len(subject['patches'])} patch(es), {subject['source']}")
    print(f"claim: {shown}: {theorem['name']} over {len(functions)} functions, "
          f"{len(theorem['axioms'])} axioms, relying on "
          f"{', '.join(relied) if relied else 'no unproven obligation'}")
    for error in errors:
        print(f"claim: ERROR {error}")
    return not errors


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--upstream", default=str(ROOT / "upstream" / "zlib"))
    args = ap.parse_args()
    files = sorted((ROOT / "claims").glob("*.toml"))
    if not files:
        print("claim: ERROR no claim in claims/")
        return 1
    return 0 if all([check(f, pathlib.Path(args.upstream)) for f in files]) else 1


if __name__ == "__main__":
    sys.exit(main())
