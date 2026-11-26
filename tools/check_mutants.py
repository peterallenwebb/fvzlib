#!/usr/bin/env python3
"""Mutation testing: change the C source a little and see that a proof breaks.

A specification that says too little is proven by too many programs.  This
script guards against that.  It makes many small changes to a verified
source file, one at a time, and checks the existing proofs against each
changed file.  Each changed file is called a mutant.

For each mutant the script

  * translates it with clightgen, under the flags in proofs/zlib.mk;
  * drops it if clightgen rejects it, or if the translation is the same as
    for the unchanged file, which means the change is in code that this
    configuration does not compile;
  * otherwise compiles the proof files, and records the first one that
    fails, and the lemma it fails in.  The first file that names a C
    function the mutant changes is compiled as early as it can be: after
    the files it needs and no others.  That only saves time.  A mutant
    survives only if every file compiles.

A mutant is "killed" when a proof file fails.  A mutant "survives" when
every proof still checks.  A survivor is either a change that makes no
difference to what the contracts promise, or a sign that a contract
promises too little.  Each survivor must be listed, with the reason it is
acceptable, in audit/mutants-<file>.toml.  The script fails if a survivor
is not listed, or if a listed mutant no longer survives.

Killed does not mean wrong.  A killed mutant may still be a correct
program whose proof would need changes.  What a kill shows is that the
proofs are about this code in detail.

The changes made:

  operator    one operator replaced by a near one:  <  by  <=  or  >=,
              +  by  -,  <<  by  >>,  &  by  |,  and so on
  constant    one integer constant raised or lowered by one
  statement   one assignment or macro call removed
  condition   the condition of one `if` or `while` negated
  variable    one use of a variable replaced by another parameter or
              local variable of the same function
  return      one returned expression raised by one
  pristine    the file as upstream released it, before our patches

Run inside the toolchain container, after `make check` and `make proofs`:

    tools/in-container.sh make mutants

Usage: tools/check_mutants.py [--jobs N] [--only REGEX] [--list]
                              [--timeout SECONDS] [--keep]
"""
import argparse
import concurrent.futures
import os
import pathlib
import re
import shlex
import shutil
import subprocess
import sys
import time
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
PATCHED = BUILD / "zlib-patched"
PRISTINE = BUILD / "zlib-pristine"
SETTINGS = ROOT / "proofs" / "zlib.mk"

# What is tested: a source file, and the directory of proofs about it.
SOURCE = "adler32.c"
PROOFS = ROOT / "proofs" / "adler32"
CLIGHT = "adler32_clight"
WORK = BUILD / "mutants" / "adler32"
ALLOW = ROOT / "audit" / "mutants-adler32.toml"

LEX = re.compile(r"""
    (?P<comment>/\*.*?\*/|//[^\n]*)
  | (?P<string>"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*')
  | (?P<number>\.?\d(?:[eEpP][+-]|[\w.])*)
  | (?P<ident>[A-Za-z_]\w*)
  | (?P<punct>\.\.\.|<<=|>>=|->|\+\+|--|<<|>>|<=|>=|==|!=|&&|\|\||[-+*/%&|^]=|\#\#|[^\s\w])
""", re.VERBOSE | re.DOTALL)

OPERATORS = {
    "<": ["<=", ">="], "<=": ["<", ">"], ">": [">=", "<="], ">=": [">", "<"],
    "==": ["!="], "!=": ["=="],
    "+": ["-"], "-": ["+"], "+=": ["-="], "-=": ["+="],
    "<<": [">>"], ">>": ["<<"], "&": ["|"], "|": ["&"],
    "&=": ["|="], "|=": ["&="], "%=": ["/="], "%": ["/"], "/": ["%"],
    "++": ["--"], "--": ["++"],
}
ASSIGN = {"=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="}
# The body of a macro names variables of the function that uses it.  The
# script does not expand macros, so it cannot tell which variables are in
# scope there.  These are the swaps it makes in a macro body.
MACRO_PARTNER = {"adler": "sum2", "sum2": "adler"}
TYPE_WORDS = {
    "unsigned", "signed", "long", "int", "short", "char", "const", "static",
    "local", "register", "volatile", "struct", "void",
    "uLong", "uInt", "Bytef", "z_size_t", "z_off_t", "z_off64_t"}
NOT_A_STATEMENT = TYPE_WORDS | {
    "return", "if", "while", "do", "for", "else", "break", "continue",
    "goto", "typedef", "sizeof"}
NUMBER = re.compile(r"(0[xX][0-9a-fA-F]+|\d+)([uUlL]*)$")


def settings():
    values = {}
    for line in SETTINGS.read_text().splitlines():
        m = re.match(r"(\w+)\s*:=\s*(.*)$", line)
        if m:
            values[m.group(1)] = m.group(2).strip()
    return values


# ---- reading the C source -------------------------------------------------

def tokens_of(text):
    """The tokens of `text` that a mutation may touch.

    Each is (start, end, kind, text).  Comments are left out.  So are
    preprocessor lines, apart from the body of a #define.  Also returns the
    start offsets of the tokens that are in the body of a #define.
    """
    spans = []          # character ranges that may be mutated
    macro_spans = []    # those of them that are the body of a #define
    pos = 0
    for line in re.finditer(r"(?:[^\n\\]|\\.|\\\n)*\n?", text):
        if not line.group():
            break
        body, start = line.group(), line.start()
        directive = re.match(r"\s*#\s*(\w+)", body)
        if not directive:
            spans.append((start, line.end()))
        elif directive.group(1) == "define":
            head = re.match(r"\s*#\s*define\s+\w+(\([^)]*\))?", body)
            spans.append((start + head.end(), line.end()))
            macro_spans.append(spans[-1])
        pos = line.end()
    out, in_macro = [], set()
    for m in LEX.finditer(text):
        if m.lastgroup == "comment":
            continue
        if any(a <= m.start() and m.end() <= b for a, b in spans):
            out.append((m.start(), m.end(), m.lastgroup, m.group()))
            if any(a <= m.start() and m.end() <= b for a, b in macro_spans):
                in_macro.add(m.start())
    return out, in_macro


def functions_of(toks, in_macro):
    """The function definitions among `toks`.

    Each is (first, last, names, declared): the indices of the braces
    around the body, the names of the parameters and local variables, and
    the indices of the tokens that declare the local variables.
    """
    code = [i for i, t in enumerate(toks) if t[0] not in in_macro]
    found, depth, k = [], 0, 0
    while k < len(code):
        i = code[k]
        tok = toks[i][3]
        if tok == "{" and depth == 0 and k > 0 and toks[code[k - 1]][3] == ")":
            # the parameters: back from the ")" to its "("
            names, d, j, piece = [], 0, k - 1, []
            while j >= 0:
                t = toks[code[j]]
                d += {")": 1, "(": -1}.get(t[3], 0)
                if d == 0 or (d == 1 and t[3] == ","):
                    last = [x for x in piece if x[2] == "ident"
                            and x[3] not in TYPE_WORDS]
                    if last:
                        names.append(last[0][3])   # piece is in reverse
                    piece = []
                    if d == 0:
                        break
                elif not (d == 1 and t[3] == ")"):
                    piece.append(t)
                j -= 1
            names.reverse()
            # the body: forward to the matching "}"
            declared, d, j, begins = set(), 0, k, False
            while j < len(code):
                t = toks[code[j]]
                d += {"{": 1, "}": -1}.get(t[3], 0)
                if d == 0:
                    break
                if begins and t[3] in TYPE_WORDS:
                    while toks[code[j]][3] != ";":
                        t = toks[code[j]]
                        declared.add(code[j])
                        if t[2] == "ident" and t[3] not in TYPE_WORDS:
                            names.append(t[3])
                        j += 1
                begins = toks[code[j]][3] in (";", "{", "}")
                j += 1
            found.append((i, code[j], names, declared))
            k = code.index(code[j], k)
        else:
            depth += {"{": 1, "}": -1}.get(tok, 0)
        k += 1
    return found


def position(text, offset):
    line = text.count("\n", 0, offset) + 1
    col = offset - (text.rfind("\n", 0, offset) + 1) + 1
    return line, col


def mutants_of(text):
    """Every mutant of `text`: a list of (name, kind, changed text)."""
    toks, in_macro = tokens_of(text)
    found = []

    def add(kind, start, end, new, label):
        line, col = position(text, start)
        found.append((f"L{line}C{col}:{label}", kind,
                      text[:start] + new + text[end:]))

    # operators, constants, variables
    for start, end, kind, tok in toks:
        if kind == "punct" and tok in OPERATORS:
            for new in OPERATORS[tok]:
                add("operator", start, end, new, f"{tok} to {new}")
        elif kind == "number":
            m = NUMBER.match(tok)
            if m:
                value = int(m.group(1), 0)
                for new in (value + 1, value - 1):
                    if new >= 0:
                        add("constant", start, end, f"{new}{m.group(2)}",
                            f"{tok} to {new}{m.group(2)}")
        elif kind == "ident" and start in in_macro and tok in MACRO_PARTNER:
            add("variable", start, end, MACRO_PARTNER[tok],
                f"{tok} to {MACRO_PARTNER[tok]}")

    # variables and returned expressions, function by function
    for first, last, names, declared in functions_of(toks, in_macro):
        for i in range(first + 1, last):
            start, end, kind, tok = toks[i]
            if kind == "ident" and tok in names and i not in declared:
                for new in names:
                    if new != tok:
                        add("variable", start, end, new, f"{tok} to {new}")
            elif tok == "return":
                j = i + 1
                while toks[j][3] != ";":
                    j += 1
                # a lone constant already has its constant mutants
                if j - i > 2:
                    a, b = toks[i + 1][0], toks[j - 1][1]
                    add("return", a, b, f"({text[a:b]}) + 1",
                        "returned value plus 1")

    # conditions: if ( c )  and  while ( c )
    for i, (start, end, kind, tok) in enumerate(toks):
        if tok in ("if", "while") and i + 1 < len(toks) and toks[i + 1][3] == "(":
            depth, j = 0, i + 1
            while j < len(toks):
                depth += {"(": 1, ")": -1}.get(toks[j][3], 0)
                if depth == 0:
                    break
                j += 1
            if j < len(toks):
                inner = text[toks[i + 1][1]:toks[j][0]]
                add("condition", toks[i + 1][1], toks[j][0],
                    f"!({inner})", f"negate {tok}")

    # statements: an assignment or a macro call, up to its semicolon
    depth, begins, cond_close = 0, True, set()
    i = 0
    while i < len(toks):
        start, end, kind, tok = toks[i]
        if tok == "(":
            if i > 0 and toks[i - 1][3] in ("if", "while") and depth == 0:
                cond_close.add("pending")
            depth += 1
        elif tok == ")":
            depth -= 1
            if depth == 0 and "pending" in cond_close:
                cond_close.discard("pending")
                begins = True
                i += 1
                continue
        elif depth == 0 and begins and kind == "ident" and tok not in NOT_A_STATEMENT:
            j, d = i, 0
            while j < len(toks):
                t = toks[j][3]
                d += {"(": 1, ")": -1}.get(t, 0)
                if d == 0 and t in (";", "{", "}"):
                    break
                j += 1
            if j < len(toks) and toks[j][3] == ";":
                body = [t[3] for t in toks[i:j]]
                call = (len(body) >= 3 and body[1] == "(" and body[-1] == ")")
                if call or any(t in ASSIGN or t in ("++", "--") for t in body):
                    add("statement", start, toks[j][0], "",
                        "remove " + " ".join(body)[:40])
        begins = depth == 0 and tok in (";", "{", "}", "else", "do")
        i += 1
    return found


# ---- checking one mutant --------------------------------------------------

def run(cmd, cwd, timeout):
    try:
        done = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                              timeout=timeout)
        return done.returncode, done.stdout + done.stderr
    except subprocess.TimeoutExpired:
        return None, "timed out"


def translate(source_text, where, defines):
    """Write `source_text` under `where` and translate it.  Returns the
    translation, or None if clightgen rejects the file."""
    (where / "src").mkdir(parents=True, exist_ok=True)
    (where / "src" / SOURCE).write_text(source_text)
    code, _ = run(["clightgen", "-normalize", "-I", str(PATCHED), *defines,
                   f"src/{SOURCE}", "-o", f"{CLIGHT}.v"], where, 120)
    out = where / f"{CLIGHT}.v"
    return out.read_text() if code == 0 and out.exists() else None


def proof_files():
    """The proof files in build order, those among them that do not depend
    on the translated C source, and the files each one requires."""
    text = (PROOFS / "Makefile").read_text().replace("\\\n", " ")
    files = re.search(r"^FILES\s*:=\s*(.*)$", text, re.M).group(1).split()
    depends, requires = {CLIGHT}, {}
    for name in files:
        if name == CLIGHT:
            continue
        source = (PROOFS / f"{name}.v").read_text()
        required = set()
        for req in re.findall(r"Require\s+(?:Import\s+|Export\s+)?([^.]*)\.", source):
            required.update(req.split())
        requires[name] = required & set(files)
        if required & depends:
            depends.add(name)
    return files, [f for f in files if f not in depends], requires


def functions_in(translation):
    """The C functions of a translation: name to Clight definition."""
    parts = re.split(r"^Definition f_(\w+) :=", translation, flags=re.M)
    return {name: re.split(r"^Definition ", body, flags=re.M)[0]
            for name, body in zip(parts[1::2], parts[2::2])}


def build_order(translated, baseline, files, requires):
    """`files`, reordered so that the first file that names a changed C
    function comes as early as it can: after the files it requires and no
    others.  Then the next such file, and so on, and last the rest.  Each
    file still comes after every file it requires, since `files` is in
    build order."""
    before, after = functions_in(baseline), functions_in(translated)
    changed = [n for n in after if after[n] != before.get(n)]
    if not changed:
        return files
    names = re.compile(r"\bf_(?:" + "|".join(map(re.escape, changed)) + r")\b")
    order = [CLIGHT]
    for name in files:
        if name == CLIGHT or not names.search((PROOFS / f"{name}.v").read_text()):
            continue
        needed, grew = {name}, True
        while grew:
            more = set().union(*(requires.get(f, set()) for f in needed)) - needed
            needed |= more
            grew = bool(more)
        order += [f for f in files if f in needed and f not in order]
    return order + [f for f in files if f not in order]


def enclosing_lemma(path, line):
    name = "the start of the file"
    for number, text in enumerate(path.read_text().splitlines(), 1):
        if number > line:
            break
        m = re.match(r"\s*(?:Lemma|Theorem|Example|Corollary|Definition|"
                     r"Fixpoint|Instance|#\[export\] Instance)\s+([\w']+)", text)
        if m:
            name = m.group(1)
    return name


def check(index, name, kind, text, baseline, defines, files, fixed, requires,
          flags, timeout, keep):
    where = WORK / f"m{index:04d}"
    if where.exists():
        shutil.rmtree(where)
    where.mkdir(parents=True)
    began = time.time()
    result = {"name": name, "kind": kind}
    translated = translate(text, where, defines)
    if translated is None:
        result["status"] = "rejected"
    elif translated == baseline:
        result["status"] = "same"
    else:
        for path in PROOFS.glob("*.v"):
            if path.stem != CLIGHT:
                shutil.copy(path, where)
        for stem in fixed:
            shutil.copy(PROOFS / f"{stem}.vo", where)
        result["status"] = "survived"
        for stem in build_order(translated, baseline, files, requires):
            if stem in fixed:
                continue
            code, output = run(["rocq", "compile", *flags, f"{stem}.v"],
                               where, timeout)
            if code == 0:
                continue
            result["file"] = stem
            if code is None:
                result["status"] = "timeout"
            else:
                result["status"] = "killed"
                at = re.search(rf'File "\./{stem}\.v", line (\d+)', output)
                error = re.findall(r"^Error:.*(?:\n(?!File ).*)*", output, re.M)
                if at and error:
                    # the last location printed is the error's
                    line = int(re.findall(
                        rf'File "\./{stem}\.v", line (\d+)', output)[-1])
                    result["lemma"] = enclosing_lemma(where / f"{stem}.v", line)
            break
    result["seconds"] = round(time.time() - began)
    if not keep and result["status"] != "survived":
        shutil.rmtree(where)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--only", help="check only mutants whose name matches")
    ap.add_argument("--list", action="store_true", help="list mutants and stop")
    ap.add_argument("--timeout", type=int, default=900,
                    help="seconds allowed for one proof file")
    ap.add_argument("--keep", action="store_true",
                    help="keep the working directory of every mutant")
    args = ap.parse_args()

    source = PATCHED / SOURCE
    if not source.exists():
        print("mutants: ERROR no patched tree; run `make check` first")
        return 1
    text = source.read_text()
    mutants = mutants_of(text)
    pristine = (PRISTINE / SOURCE).read_text()
    if pristine != text:
        mutants.append(("pristine", "pristine", pristine))
    if args.only:
        mutants = [m for m in mutants if re.search(args.only, m[0])]
    if args.list:
        for name, kind, _ in mutants:
            print(f"{kind:10} {name}")
        print(f"{len(mutants)} mutants")
        return 0

    files, fixed, requires = proof_files()
    missing = [f for f in fixed if not (PROOFS / f"{f}.vo").exists()]
    if missing:
        print("mutants: ERROR the proofs are not built; run `make proofs` first")
        return 1
    defines = shlex.split(settings()["ZLIB_DEFINES"])
    flags = ["-Q", ".", "fvzlib.proofs.adler32",
             "-Q", str(ROOT / "proofs" / "lib"), "fvzlib.proofs.lib",
             "-Q", str(ROOT / "spec" / "format"), "fvzlib.format",
             "-Q", str(ROOT / "spec" / "api"), "fvzlib.api"]
    WORK.mkdir(parents=True, exist_ok=True)
    baseline = translate(text, WORK / "baseline", defines)
    if baseline is None:
        print("mutants: ERROR clightgen rejects the unchanged file")
        return 1

    began = time.time()
    results = [None] * len(mutants)
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        jobs = {pool.submit(check, i, name, kind, changed, baseline, defines,
                            files, fixed, requires, flags, args.timeout,
                            args.keep): i
                for i, (name, kind, changed) in enumerate(mutants)}
        for done, job in enumerate(concurrent.futures.as_completed(jobs), 1):
            results[jobs[job]] = job.result()
            if done % 20 == 0 or done == len(mutants):
                print(f"mutants: {done} of {len(mutants)} checked",
                      file=sys.stderr, flush=True)

    # ---- report ----
    allowed = {}
    if ALLOW.exists():
        for entry in tomllib.loads(ALLOW.read_text()).get("survivor", []):
            allowed[entry["name"]] = entry["reason"]
    lines, errors = [], []
    for r in results:
        detail = ""
        if r["status"] in ("killed", "timeout"):
            detail = f"  {r['file']}.v" + (f", {r['lemma']}" if "lemma" in r else "")
        elif r["status"] == "survived":
            reason = allowed.get(r["name"])
            detail = (f"  accepted in {ALLOW.relative_to(ROOT)}" if reason
                      else "  NOT ACCEPTED")
            if not reason:
                errors.append(f"{r['name']} survives and is not listed in "
                              f"{ALLOW.relative_to(ROOT)}")
        lines.append(f"{r['status']:9} {r['kind']:10} {r['name']}{detail}")
    survived = {r["name"] for r in results if r["status"] == "survived"}
    if not args.only:
        for name in allowed:
            if name not in survived:
                errors.append(f"{name} is listed as a survivor but does not "
                              f"survive")
    count = {s: sum(1 for r in results if r["status"] == s)
             for s in ("killed", "timeout", "survived", "same", "rejected")}
    live = count["killed"] + count["timeout"] + count["survived"]
    by_file = {}
    for r in results:
        if r["status"] in ("killed", "timeout"):
            by_file[r["file"]] = by_file.get(r["file"], 0) + 1
    summary = [
        f"source: {SOURCE} of the patched tree, {len(results)} mutants made",
        f"dropped: {count['rejected']} that clightgen rejects, "
        f"{count['same']} that change nothing in this configuration",
        f"checked: {live}",
        f"killed: {count['killed']}"
        + (f", and {count['timeout']} more where a proof ran out of time"
           if count["timeout"] else ""),
        "killed by: " + ", ".join(f"{f}.v {n}" for f, n in
                                  sorted(by_file.items(), key=lambda x: -x[1])),
        f"survived: {count['survived']}, of which "
        f"{sum(1 for n in survived if n in allowed)} are accepted with a reason",
        f"time: {round(time.time() - began)} seconds with {args.jobs} jobs",
    ]
    (WORK / "report.txt").write_text("\n".join(summary + [""] + lines) + "\n")
    for line in summary:
        print(f"mutants: {line}")
    for r in results:
        if r["status"] in ("survived", "timeout"):
            print(f"mutants: {r['status']}: {r['name']}"
                  + ("  (accepted)" if r["name"] in allowed else ""))
    for e in errors:
        print(f"mutants: ERROR {e}")
    print(f"mutants: full list in {(WORK / 'report.txt').relative_to(ROOT)}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
