#!/usr/bin/env python3
"""Differential test: the Adler-32 reference model against the real zlib.

The reference model is the Rocq definitions of Layers 1 and 2.  This script
checks that zlib, as a C compiler builds it, returns what the model says,
on several thousand inputs.

It

  * builds the zlib library three ways, each from a copy of a tree under
    build/, with the upstream ./configure and makefile:

      pristine   zlib as released
      patched    zlib with our patch sequence, as verified
      checked    the patched tree, compiled with the address and
                 undefined-behavior checkers of the C compiler

  * builds tests/differential/adler32_cases.c against each library and
    runs it.  The program calls the Adler-32 functions and prints each
    input with the value zlib returned;
  * requires the three outputs to be the same, and the checked build to
    report nothing.  Each input is in a block of memory of exactly its
    length, so the address checker sees a read outside the buffer;
  * requires zlib to return, for each test vector of
    spec/format/Adler32Tests.v, the value written in that file;
  * writes the cases as a Rocq file and compiles it with
    tests/differential/Adler32Harness.v.  Rocq evaluates the model on each
    input and the file compiles only if every value agrees with zlib's;
  * checks that the comparison can fail: for one case of each kind it
    changes zlib's value by one and requires the compilation to fail.

Agreement on these inputs is evidence, not proof.  The proofs in proofs/
are what cover every input.  This test adds two things the proofs do not
give: it runs the library as gcc builds it, not as CompCert reads it, and
it runs pristine zlib as well as the patched source.

Run inside the toolchain container, after `make check`:

    tools/in-container.sh make differential

Writes build/differential.txt.
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
WORK = BUILD / "differential"
TESTS = ROOT / "tests" / "differential"
VECTORS = ROOT / "spec" / "format" / "Adler32Tests.v"
GENERATOR = "adler32_cases"
CHECKERS = "-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all"

# name, tree to copy, CFLAGS for ./configure and the generator
VARIANTS = [
    ("pristine", BUILD / "zlib-pristine", None),
    ("patched", BUILD / "zlib-patched", None),
    ("checked", BUILD / "zlib-patched", CHECKERS),
]
ROCQ_FLAGS = ["-Q", str(ROOT / "spec" / "format"), "fvzlib.format",
              "-Q", str(ROOT / "spec" / "api"), "fvzlib.api",
              "-Q", ".", "fvzlib.tests.differential"]
GROUP = 100         # cases in one Rocq definition


class Failed(Exception):
    pass


def run(cmd, cwd, env=None, timeout=1800):
    return subprocess.run(cmd, cwd=cwd, env=env, text=True, timeout=timeout,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def must(result, what):
    if result.returncode != 0:
        raise Failed(f"{what} failed\n{result.stdout[-2000:]}"
                     f"{result.stderr[-4000:]}")
    return result


# ---- zlib's side ----------------------------------------------------------

def zlib_output(name, tree, cflags):
    """Build the library and the generator in a copy of `tree`, run the
    generator, and return what it printed."""
    where = WORK / name
    if where.exists():
        shutil.rmtree(where)
    shutil.copytree(tree, where)
    env = dict(os.environ)
    if cflags:
        env["CFLAGS"] = cflags
    must(run(["./configure"], where, env), f"{name}: ./configure")
    must(run(["make", "libz.a"], where, env), f"{name}: make libz.a")
    if cflags:
        # the checkers must really be compiled into zlib's own code
        symbols = must(run(["nm", "adler32.o"], where), f"{name}: nm").stdout
        for checker in ("__asan_", "__ubsan_"):
            if checker not in symbols:
                raise Failed(f"{name}: adler32.o was built without "
                             f"{checker.strip('_')}")
    flags = (cflags or "-O2").split()
    must(run(["cc", *flags, "-Wall", "-Wextra", "-I", ".",
              str(TESTS / f"{GENERATOR}.c"), "libz.a", "-o", GENERATOR],
             where, env), f"{name}: compiling {GENERATOR}.c")
    env["ASAN_OPTIONS"] = "detect_leaks=0:abort_on_error=0"
    env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"
    out = run([f"./{GENERATOR}"], where, env)
    if out.returncode != 0:
        raise Failed(f"{name}: {GENERATOR} exited with status "
                     f"{out.returncode}\n{out.stderr[-4000:]}")
    notes = out.stderr.strip().splitlines()
    if len(notes) != 1 or not re.fullmatch(r"\d+ calls to zlib", notes[0]):
        raise Failed(f"{name}: {GENERATOR} wrote to standard error:\n"
                     f"{out.stderr[-4000:]}")
    return out.stdout, int(notes[0].split()[0])


# ---- the model's side -----------------------------------------------------

def rocq_data(text):
    kind, _, rest = text.partition(":")
    if kind == "hex":
        if not re.fullmatch(r"(?:[0-9a-f]{2})*", rest):
            raise Failed(f"bad data: {text[:60]}")
        return f'(Hex "{rest}")'
    if kind == "run":
        count, first, step = (int(x) for x in rest.split(":"))
        return f"(Run {count} {first} {step})"
    raise Failed(f"bad data: {text[:60]}")


def data_length(text):
    kind, _, rest = text.partition(":")
    return len(rest) // 2 if kind == "hex" else int(rest.split(":")[0])


def parse(line):
    """One line of the generator: (kind, Rocq term builder, bytes of input).

    The builder takes the amount to add to zlib's value, so that the
    self-test can make a case that must fail."""
    words = line.split()
    kind = words[0]
    if kind == "initial":
        return kind, lambda d: f"Initial {int(words[1]) + d}", 0
    if kind in ("whole", "prose"):
        data, result = rocq_data(words[1]), int(words[2])
        return (kind, lambda d: f"{kind.capitalize()} {data} {result + d}",
                data_length(words[1]))
    if kind in ("pieces", "vector"):
        rest = words[1:] if kind == "pieces" else words[2:]
        result = int(rest[0])
        data = "[" + "; ".join(rocq_data(w) for w in rest[1:]) + "]"
        return (kind, lambda d: f"Pieces {data} {result + d}",
                sum(data_length(w) for w in rest[1:]))
    if kind == "combine":
        a1, a2, len2, result = (int(w) for w in words[1:])
        return (kind,
                lambda d: f"Combine {a1} {a2} {len2} {result + d}", 0)
    if kind == "joined":
        d1, d2 = rocq_data(words[1]), rocq_data(words[2])
        a1, a2, result = (int(w) for w in words[3:])
        return (kind,
                lambda d: f"Joined {d1} {d2} {a1} {a2} {result + d}",
                data_length(words[1]) + data_length(words[2]))
    raise Failed(f"unknown line: {line[:60]}")


HEADER = """(* Generated by tools/check_differential.py.  Do not edit. *)
From Stdlib Require Import ZArith List PrimString.
From fvzlib.tests.differential Require Import Adler32Harness.
Import ListNotations.
Local Open Scope pstring_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
"""


def rocq_file(terms):
    out = [HEADER]
    groups = [terms[i:i + GROUP] for i in range(0, len(terms), GROUP)]
    for n, group in enumerate(groups):
        out.append(f"Definition cases_{n} : list case := [\n  "
                   + ";\n  ".join(group) + "\n].\n")
    out.append("Definition cases : list case :=\n  "
               + " ++ ".join(f"cases_{n}" for n in range(len(groups))) + ".\n")
    out.append(f"Example count : Z.of_nat (List.length cases) = {len(terms)}.\n"
               "Proof. vm_compute. reflexivity. Qed.\n")
    # The model is evaluated once, when the kernel checks this at Qed.
    out.append("Example all_agree : failures cases = [].\n"
               "Proof. vm_cast_no_check (eq_refl (@nil Z)). Qed.\n")
    return "\n".join(out)


def differing(where):
    """After a failed comparison: the positions Rocq finds to differ."""
    text = (where / "Adler32Cases.v").read_text()
    text = text[:text.index("Example all_agree")]
    (where / "Differing.v").write_text(
        text + "Eval vm_compute in failures cases.\n")
    return compile_rocq(where, "Differing").stdout.strip()


def compile_rocq(where, name):
    return run(["rocq", "compile", *ROCQ_FLAGS, f"{name}.v"], where)


def vector_values():
    """The expected value of each test vector in Adler32Tests.v."""
    text = re.sub(r"\(\*.*?\*\)", "", VECTORS.read_text(), flags=re.S)
    values = {}
    for example in text.split("Example")[1:]:
        statement = example.split("Proof")[0]
        m = re.search(r"=\s*(0x[0-9a-fA-F]+|\d+)\s*\.\s*$", statement)
        if m:       # an example whose right-hand side is one number
            values[statement.split()[0]] = int(m.group(1), 0)
    return values


def main():
    for _, tree, _ in VARIANTS:
        if not (tree / "zlib.h").exists():
            print("differential: ERROR no zlib trees; run `make check` first")
            return 1
    if not (ROOT / "spec" / "api" / "Adler32Facts.vo").exists():
        print("differential: ERROR the specifications are not compiled; "
              "run `make` first")
        return 1
    WORK.mkdir(parents=True, exist_ok=True)
    report, began = [], time.time()
    cc = run(["cc", "--version"], ROOT).stdout.splitlines()
    report.append(f"C compiler: {cc[0] if cc else 'unknown'}")

    # ---- zlib's side ----
    outputs = {}
    for name, tree, cflags in VARIANTS:
        outputs[name], calls = zlib_output(name, tree, cflags)
        report.append(f"{name}: built with ./configure and make"
                      + (f", CFLAGS={cflags}" if cflags else "")
                      + f"; {calls} calls to zlib, "
                      f"{len(outputs[name].splitlines())} cases")
    first = outputs["patched"]
    for name in outputs:
        if outputs[name] != first:
            raise Failed(f"the {name} build and the patched build return "
                         f"different values; compare build/differential/"
                         f"{name}.txt and patched.txt")
    for name in outputs:
        (WORK / f"{name}.txt").write_text(outputs[name])
    report.append("the three builds return the same value in every case, "
                  "and the checked build reports nothing")

    lines = first.splitlines()
    parsed = [parse(line) for line in lines]
    kinds = {}
    for kind, _, size in parsed:
        n, total = kinds.get(kind, (0, 0))
        kinds[kind] = (n + 1, total + size)

    # ---- the test vectors ----
    expected = vector_values()
    seen = {}
    for line in lines:
        words = line.split()
        if words[0] == "vector":
            seen[words[1]] = int(words[2])
    if not expected or set(seen) != set(expected):
        raise Failed("the test vectors of Adler32Tests.v and of the "
                     f"generator differ: {sorted(set(seen) ^ set(expected))}")
    for name in expected:
        if seen[name] != expected[name]:
            raise Failed(f"vector {name}: zlib returns {seen[name]:#x}, "
                         f"Adler32Tests.v has {expected[name]:#x}")
    report.append(f"test vectors: zlib returns the value in Adler32Tests.v "
                  f"for all {len(expected)}")

    # ---- the model's side ----
    rocq = WORK / "rocq"
    if rocq.exists():
        shutil.rmtree(rocq)
    rocq.mkdir()
    shutil.copy(TESTS / "Adler32Harness.v", rocq)
    must(compile_rocq(rocq, "Adler32Harness"), "compiling Adler32Harness.v")
    (rocq / "Adler32Cases.v").write_text(
        rocq_file([build(0) for _, build, _ in parsed]))
    started = time.time()
    result = compile_rocq(rocq, "Adler32Cases")
    if result.returncode != 0:
        raise Failed("the model and zlib differ, or the cases do not "
                     "compile\n" + result.stderr[-2000:]
                     + "\nthe cases that differ, by position counted from "
                     "0 in build/differential/patched.txt:\n"
                     + differing(rocq)[-2000:])
    report.append(f"model: Rocq evaluated the model on all {len(parsed)} "
                  f"cases and every value agrees with zlib's "
                  f"({round(time.time() - started)} seconds)")
    for kind in kinds:
        n, total = kinds[kind]
        report.append(f"  {kind:8} {n:5} cases"
                      + (f", {total} bytes of input" if total else ""))

    # ---- the comparison can fail ----
    for kind in kinds:
        build = next(b for k, b, _ in parsed if k == kind)
        (rocq / "Altered.v").write_text(rocq_file([build(1)]))
        result = compile_rocq(rocq, "Altered")
        if result.returncode == 0 or "failures cases" not in result.stderr:
            raise Failed(f"self-test: a {kind} case with zlib's value "
                         f"changed by one was not caught\n"
                         + result.stderr[-2000:])
    report.append(f"self-test: a changed value is caught for each of the "
                  f"{len(kinds)} kinds of case")
    report.append(f"time: {round(time.time() - began)} seconds")

    (BUILD / "differential.txt").write_text("\n".join(report) + "\n")
    for line in report:
        print(f"differential: {line}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Failed as e:
        print(f"differential: ERROR {e}")
        sys.exit(1)
