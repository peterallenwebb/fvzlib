#!/usr/bin/env python3
"""Check the reviews of preconditions in audit/preconditions-*.toml.

A review file lists every clause of the precondition of every contract in
one directory of C proofs, with a verdict and a reason for each.  This
tool keeps the review in step with the contracts.  It checks that:

  * every contract defined in the directory is reviewed, or listed as
    derived from a reviewed contract by a lemma that exists, or listed as
    the form with ticks of a reviewed contract;
  * for a form with ticks, the lemmas exist that tie it to the reviewed
    contract: that it and the generated form follow from each other, and
    that the generated form is made from the reviewed contract;
  * the clauses of each reviewed contract, read from its Rocq source, are
    exactly the clauses the review lists, in the same order;
  * each definition a clause refers to is reviewed, and the text of the
    definition recorded in the review is the text in the source;
  * each clause listed for a definition occurs in that text;
  * each verdict is a known one and comes with a reason, and each verdict
    that asks something of the caller says how the caller can meet it;
  * each Rocq result named as evidence is defined in the sources.

It reads source text only and compiles nothing.  It does not judge the
reasons.  What it guarantees is that a precondition cannot be added or
changed without the review being changed too.

Usage: tools/check_preconditions.py
"""
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent

# What a verdict says about a clause.
VERDICTS = {
    "type": "only gives an argument its C type",
    "names": "only says which value is passed",
    "nothing": "asks nothing of the caller",
    "defined": "refers to a definition reviewed under its own name",
    "needed": "the code cannot do without it",
    "promise": "a condition on the promised result, not on the call",
    "limit": "stricter than C requires: a limit of the tools",
    "ticks": "about the counter that only the function with ticks has",
}
ASKS_CALLER = {"needed", "promise", "limit"}
PARTS = ("PROP", "PARAMS", "GLOBALS", "SEP")
CONTRACT = re.compile(r"^Definition\s+(\w+)\s*:\s*ident\s*\*\s*funspec\s*:=", re.M)
RESULT = r"^\s*(?:Lemma|Theorem|Example|Corollary)\s+%s\b"


def squash(text):
    return " ".join(text.split())


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


def sentence_from(text, start):
    """The Rocq sentence that starts at `start`: up to a period followed by
    white space."""
    end = re.compile(r"\.(?=\s|$)").search(text, start)
    return text[start:end.start()] if end else text[start:]


def group_after(text, start):
    """The parenthesized group that follows position `start`, without its
    outer parentheses, and the position after it."""
    open_at = text.index("(", start)
    depth = 0
    for i in range(open_at, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return text[open_at + 1:i], i + 1
    raise ValueError("unbalanced parentheses")


def split_clauses(group):
    """Split at the semicolons that are outside every parenthesis."""
    parts, depth, current = [], 0, []
    for ch in group:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == ";" and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(ch)
    parts.append("".join(current))
    return [squash(p) for p in parts if p.strip()]


def contracts_in(text):
    """Map each contract defined in `text` to its precondition, as a list
    of (part, clause)."""
    found = {}
    for match in CONTRACT.finditer(text):
        body = sentence_from(text, match.end())
        pre = body[body.index("PRE"):body.index("POST")]
        clauses = []
        for part in PARTS:
            at = re.search(r"\b%s\b" % part, pre)
            if not at:
                continue
            group, _ = group_after(pre, at.end())
            clauses += [(part, c) for c in split_clauses(group)]
        found[match.group(1)] = clauses
    return found


def definition_text(text, name):
    match = re.search(r"^(?:Definition|Fixpoint|Inductive)\s+%s\b" % re.escape(name),
                      text, re.M)
    if not match:
        return None
    return squash(sentence_from(text, match.start()))


def sources(directories):
    texts = {}
    for directory in directories:
        for path in sorted((ROOT / directory).glob("*.v")):
            texts[path.relative_to(ROOT).as_posix()] = strip_comments(path.read_text())
    return texts


def check_verdict(entry, where, definitions, texts, errors):
    verdict = entry.get("verdict")
    if verdict not in VERDICTS:
        errors.append(f"{where}: unknown verdict {verdict!r}")
        return
    if not entry.get("reason", "").strip():
        errors.append(f"{where}: no reason given")
    if verdict in ASKS_CALLER and not entry.get("caller", "").strip():
        errors.append(f"{where}: verdict '{verdict}' needs a `caller` entry")
    if verdict == "defined" and entry.get("definition") not in definitions:
        errors.append(f"{where}: refers to {entry.get('definition')!r}, "
                      "which the review does not cover")
    for name in entry.get("checked_by", []):
        pattern = re.compile(RESULT % re.escape(name), re.M)
        if not any(pattern.search(t) for t in texts.values()):
            errors.append(f"{where}: no result named {name} in the sources")


def check(path):
    review = tomllib.loads(path.read_text())
    errors = []
    texts = sources([review["directory"], *review.get("evidence_in", [])])
    proof_texts = {f: t for f, t in texts.items()
                   if f.startswith(review["directory"] + "/")}
    defined = {}
    for file, text in proof_texts.items():
        for name, clauses in contracts_in(text).items():
            defined[name] = (file, clauses)
    definitions = {d["name"]: d for d in review.get("definition", [])}
    reviewed = {c["name"]: c for c in review.get("contract", [])}
    derived = {d["name"]: d for d in review.get("derived", [])}
    ticked = {d["name"]: d for d in review.get("ticked", [])}
    counts = dict.fromkeys(VERDICTS, 0)

    for name in sorted(defined):
        if name not in reviewed and name not in derived and name not in ticked:
            errors.append(f"{defined[name][0]}: contract {name} is not reviewed")
    for name in sorted(set(reviewed) | set(derived) | set(ticked)):
        if name not in defined:
            errors.append(f"{name}: no such contract in {review['directory']}")

    def proven(name):
        pattern = re.compile(RESULT % re.escape(name or "?"), re.M)
        return any(pattern.search(t) for t in proof_texts.values())

    for name, entry in derived.items():
        if entry.get("from") not in reviewed and entry.get("from") not in ticked:
            errors.append(f"{name}: derived from {entry.get('from')!r}, "
                          "which is not a reviewed contract")
        if not proven(entry.get("by")):
            errors.append(f"{name}: no lemma named {entry.get('by')!r}")

    for name, entry in ticked.items():
        if entry.get("plain") not in reviewed:
            errors.append(f"{name}: the form with ticks of "
                          f"{entry.get('plain')!r}, which is not reviewed")
        if "with_ticks" not in definitions:
            errors.append(f"{name}: the review does not cover with_ticks")
        for key in ("gives_generated", "from_generated", "two_forms"):
            if not proven(entry.get(key)):
                errors.append(f"{name}: no lemma named {entry.get(key)!r} "
                              f"for `{key}`")

    for name, entry in reviewed.items():
        if name not in defined:
            continue
        file, clauses = defined[name]
        listed = [(c.get("part"), squash(c.get("text", "")))
                  for c in entry.get("clause", [])]
        if listed != clauses:
            errors.append(f"{file}: the precondition of {name} is not what "
                          "the review lists")
            for part, text in clauses:
                if (part, text) not in listed:
                    errors.append(f"    in the source, not reviewed: {part} {text}")
            for part, text in listed:
                if (part, text) not in clauses:
                    errors.append(f"    reviewed, not in the source: {part} {text}")
            if sorted(listed) == sorted(clauses):
                errors.append("    the same clauses, in another order")
        for clause in entry.get("clause", []):
            where = f"{name}: {clause.get('part')} {squash(clause.get('text', ''))}"
            check_verdict(clause, where, definitions, texts, errors)
            if clause.get("verdict") in counts:
                counts[clause["verdict"]] += 1

    for name, entry in definitions.items():
        text = texts.get(entry.get("file"))
        actual = definition_text(text, name) if text is not None else None
        if actual is None:
            errors.append(f"{name}: not defined in {entry.get('file')}")
            continue
        if squash(entry.get("text", "")) != actual:
            errors.append(f"{entry['file']}: the definition of {name} is not "
                          "the text the review records")
            errors.append(f"    in the source: {actual}")
        for clause in entry.get("clause", []):
            text = squash(clause.get("text", ""))
            where = f"{name}: {text}"
            if text not in actual:
                errors.append(f"{where}: not in the definition")
            check_verdict(clause, where, definitions, texts, errors)
            if clause.get("verdict") in counts:
                counts[clause["verdict"]] += 1
        if not entry.get("clause"):
            errors.append(f"{name}: no clause reviewed")

    shown = path.relative_to(ROOT)
    print(f"preconditions: {shown}: {len(reviewed)} contracts reviewed, "
          f"{len(ticked)} forms with ticks, {len(derived)} derived from "
          f"them, {len(definitions)} definitions")
    print("preconditions: verdicts: "
          + ", ".join(f"{counts[v]} {v}" for v in VERDICTS if counts[v]))
    for error in errors:
        print(f"preconditions: ERROR {error}")
    return not errors


def main():
    files = sorted((ROOT / "audit").glob("preconditions-*.toml"))
    if not files:
        print("preconditions: ERROR no review file in audit/")
        return 1
    return 0 if all([check(f) for f in files]) else 1


if __name__ == "__main__":
    sys.exit(main())
