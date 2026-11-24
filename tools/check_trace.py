#!/usr/bin/env python3
"""Check the traceability files in trace/.

For every file trace/*.toml this checks that:

  * each source document has the recorded SHA-256;
  * each passage occurs exactly once in its source, between its recorded
    `before` and `after` text, and equals its sentences joined in order;
  * each sentence has the recorded SHA-256 and a known status;
  * each name in `covered_by` is defined in the Rocq sources;
  * `definition`, `theorem`, and `test` entries name at least one item, and
    `pending` and `not-covered` entries give a reason.

Sources that live in the upstream zlib tree are read from the directory
given by --upstream.  Without it those passages are skipped and reported.
With --strict a skipped passage is an error.

Usage: tools/check_trace.py [--upstream DIR] [--strict]
"""
import argparse
import hashlib
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
STATUSES = {"definition", "theorem", "test", "pending", "not-covered"}
NEEDS_ITEMS = {"definition", "theorem", "test"}
NEEDS_NOTE = {"pending", "not-covered"}
DEFINING = r"(?:Definition|Fixpoint|Theorem|Lemma|Example|Inductive|Record)"


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def normalize(raw, strip):
    """Drop lines matching a strip pattern, then collapse white space."""
    kept = []
    for line in raw.splitlines():
        if any(re.match(p, line) for p in strip):
            continue
        kept.append(line.replace("\f", " "))
    return " ".join(" ".join(kept).split())


def logical_roots():
    """Map Rocq logical prefixes to directories, from _CoqProject."""
    roots = {}
    for line in (ROOT / "_CoqProject").read_text().splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0] == "-Q":
            roots[parts[2]] = ROOT / parts[1]
    return roots


def resolve(name, roots):
    """Return an error string, or None if `name` is defined in the sources."""
    for prefix, directory in sorted(roots.items(), key=lambda kv: -len(kv[0])):
        if name.startswith(prefix + "."):
            rest = name[len(prefix) + 1:].split(".")
            if len(rest) != 2:
                return f"{name}: expected {prefix}.<File>.<name>"
            path = directory / (rest[0] + ".v")
            if not path.exists():
                return f"{name}: no file {path.relative_to(ROOT)}"
            pattern = rf"^\s*{DEFINING}\s+{re.escape(rest[1])}\b"
            if not re.search(pattern, path.read_text(), re.M):
                return f"{name}: not defined in {path.relative_to(ROOT)}"
            return None
    return f"{name}: no logical root matches"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--upstream", help="directory holding the upstream zlib tree")
    ap.add_argument("--strict", action="store_true",
                    help="treat a skipped passage as an error")
    args = ap.parse_args()

    roots = logical_roots()
    errors, skipped, counts = [], [], {}
    files = sorted((ROOT / "trace").glob("*.toml"))
    if not files:
        errors.append("no files in trace/")

    for file in files:
        rel = file.relative_to(ROOT)
        doc = tomllib.loads(file.read_text())
        texts = {}
        for sid, src in doc.get("sources", {}).items():
            if "path" in src:
                path = ROOT / src["path"]
            elif args.upstream:
                path = pathlib.Path(args.upstream) / src["upstream_path"]
            else:
                texts[sid] = None
                continue
            if not path.exists():
                errors.append(f"{rel}: source {sid}: {path} not found")
                texts[sid] = None
                continue
            raw = path.read_bytes()
            if sha256_bytes(raw) != src["sha256"]:
                errors.append(f"{rel}: source {sid}: SHA-256 differs from the "
                              f"recorded one; the document has changed")
            texts[sid] = normalize(raw.decode("latin-1"), src.get("strip", []))

        for passage in doc.get("passage", []):
            pid = passage["id"]
            sentences = passage.get("sentence", [])
            if not sentences:
                errors.append(f"{rel}: {pid}: no sentences")
            for i, s in enumerate(sentences, 1):
                where = f"{rel}: {pid} sentence {i}"
                text = s["text"]
                if text != " ".join(text.split()):
                    errors.append(f"{where}: text is not white-space normalized")
                if sha256_bytes(text.encode()) != s.get("sha256"):
                    errors.append(f"{where}: sha256 does not match the text")
                status = s.get("status")
                if status not in STATUSES:
                    errors.append(f"{where}: unknown status {status!r}")
                    continue
                counts[status] = counts.get(status, 0) + 1
                items = s.get("covered_by", [])
                if status in NEEDS_ITEMS and not items:
                    errors.append(f"{where}: status {status} needs covered_by")
                if status in NEEDS_NOTE and not s.get("note"):
                    errors.append(f"{where}: status {status} needs a note")
                for name in items:
                    problem = resolve(name, roots)
                    if problem:
                        errors.append(f"{where}: {problem}")

            source = texts.get(passage["source"], "missing")
            if source == "missing":
                errors.append(f"{rel}: {pid}: unknown source {passage['source']}")
                continue
            if source is None:
                skipped.append(f"{rel}: {pid}")
                continue
            body = " ".join(s["text"] for s in sentences)
            framed = " ".join(x for x in (passage["before"], body, passage["after"]) if x)
            if source.count(body) != 1:
                errors.append(f"{rel}: {pid}: passage occurs {source.count(body)} "
                              f"times in the source, expected exactly once")
            elif framed not in source:
                errors.append(f"{rel}: {pid}: passage is not directly between "
                              f"its `before` and `after` text")
            elif not passage["after"] and not source.endswith(body):
                errors.append(f"{rel}: {pid}: empty `after`, but the passage "
                              f"does not end the document")

    total = sum(counts.values())
    summary = ", ".join(f"{counts.get(s, 0)} {s}" for s in sorted(STATUSES))
    print(f"trace: {total} sentences in {len(files)} file(s): {summary}")
    for item in skipped:
        print(f"trace: SKIPPED {item} (needs --upstream)")
    for e in errors:
        print(f"trace: ERROR {e}")
    if errors or (skipped and args.strict):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
