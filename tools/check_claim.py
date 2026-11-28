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
  * the results about executions, if any are listed, each exist and have
    their assumptions printed in their own audit file, the further axioms
    are exactly those in audit/execution-axioms.txt, each hypothesis is
    defined, and the program they are about is there;
  * every entry of the ledger is listed with a role, an entry the claim
    relies on as unproven is still unproven, one it relies on as proven
    has that status, and a finding is still a finding;
  * the prose names the commit, each patch, each flag, each version, each
    theorem, each axiom, each hypothesis, each function, each contract,
    and each ledger entry.

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
ROLES = {"finding", "relied on", "relied on, proven", "not relied on"}


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


def axiom_names(file="allowed-axioms.txt"):
    """The names in a list of axioms in audit/: the word before each colon
    that starts an entry."""
    names, fresh = [], True
    for line in (ROOT / "audit" / file).read_text().splitlines():
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

    # ---- the results about executions ----
    runs = ref.get("executions")
    if runs:
        run_audit_path = ROOT / runs["audit"]
        run_audit = (strip_comments(run_audit_path.read_text())
                     if run_audit_path.exists() else "")
        need(run_audit, f"{runs['audit']}: no such file")
        need((ROOT / runs["program"]).exists(),
             f"{runs['program']}: no such file")
        named("the program", runs["program"])
        for result in runs.get("theorem", []):
            where = ROOT / result["file"]
            body = strip_comments(where.read_text()) if where.exists() else ""
            need(re.search(r"^Theorem\s+%s\b" % re.escape(result["name"]),
                           body, re.M),
                 f"no theorem {result['name']} in {result['file']}")
            need(re.search(r"^Print Assumptions\s+%s\.%s\."
                           % (where.stem, result["name"]), run_audit, re.M),
                 f"{runs['audit']} does not print the assumptions of "
                 f"{where.stem}.{result['name']}")
            named("the theorem", result["name"])
        need(sorted(runs["axioms"]) == sorted(axiom_names("execution-axioms.txt")),
             "the further axioms are not those of audit/execution-axioms.txt")
        for axiom in runs["axioms"]:
            named("the axiom", axiom)
        defined_in = ROOT / runs["hypotheses_in"]
        stated = (strip_comments(defined_in.read_text())
                  if defined_in.exists() else "")
        for hypothesis in runs["hypotheses"]:
            need(re.search(r"^Definition\s+%s\b" % re.escape(hypothesis),
                           stated, re.M),
                 f"no definition of {hypothesis} in {runs['hypotheses_in']}")
            named("the hypothesis", hypothesis)

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
        if item.get("role") == "relied on, proven":
            need(status.startswith("Proven") and "unproven" not in status.lower(),
                 f"{entry}: relied on as proven, but its status is: {status}")
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
    if runs:
        print(f"claim: {shown}: {len(runs.get('theorem', []))} results about "
              f"executions, {len(runs['axioms'])} further axioms, "
              f"{len(runs['hypotheses'])} hypotheses")
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
