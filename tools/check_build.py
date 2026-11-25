#!/usr/bin/env python3
"""Check that the source given to the verifier is the source that is built.

The proofs are about what clightgen reads: a zlib source file from the
patched tree, preprocessed under the flags in proofs/zlib.mk.  The upstream
build compiles something that could differ: ./configure edits zconf.h and
chooses compiler flags for the machine it runs on.

This script closes that gap mechanically.  It

  * copies the patched tree and runs the upstream ./configure there, with
    its defaults;
  * asks the upstream Makefile which commands compile each verified source
    file, for the static and for the shared library;
  * preprocesses the file with each of those commands, and with clightgen
    under the verifier's flags;
  * keeps, from each result, the tokens that come from files of the zlib
    tree, and requires the token sequences to be equal.

Declarations that come from system headers are not compared.  They are not
zlib code, and the two preprocessors read them under different predefined
macros.  A macro from a system header that is used in zlib code is compared,
because its expansion lands in a zlib file.

A known, harmless difference can be listed in env/build-check-allow.toml
with its reason.  The report says how often each such entry was used.

Run after tools/check_patches.py, inside the project's opam switch.

Usage: tools/check_build.py [--defines "FLAGS"]
"""
import argparse
import difflib
import pathlib
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
PATCHED = BUILD / "zlib-patched"
CONFIGURED = BUILD / "zlib-configured"
SETTINGS = ROOT / "proofs" / "zlib.mk"
ALLOW = ROOT / "env" / "build-check-allow.toml"
LIBRARY = ["adler32", "compress", "crc32", "deflate", "gzclose", "gzlib",
           "gzread", "gzwrite", "infback", "inffast", "inflate", "inftrees",
           "trees", "uncompr", "zutil"]

TOKEN = re.compile(r"""
    (?:u8|[uUL])?"(?:\\.|[^"\\])*"        # string literal
  | (?:[uUL])?'(?:\\.|[^'\\])*'           # character constant
  | \.?\d(?:[eEpP][+-]|[\w.])*            # number
  | [A-Za-z_]\w*                          # identifier or keyword
  | \.\.\.|<<=|>>=|->|\+\+|--|<<|>>|<=|>=|==|!=|&&|\|\||[-+*/%&|^]=|\#\#
  | \S                                    # any other single character
""", re.VERBOSE)
MARKER = re.compile(r'#\s*(?:line\s+)?(\d+)\s+"((?:\\.|[^"\\])*)"')


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def settings():
    """Read the NAME := value lines of proofs/zlib.mk."""
    values = {}
    for line in SETTINGS.read_text().splitlines():
        m = re.match(r"(\w+)\s*:=\s*(.*)$", line)
        if m:
            values[m.group(1)] = m.group(2).strip()
    return values


def tree_tokens(text, tree, cwd):
    """The tokens of preprocessed `text` that come from files under `tree`.

    Returns a list of (file, line, token), with file relative to the tree.
    """
    tree = tree.resolve()
    out, current, lineno = [], None, 0
    for line in text.splitlines():
        m = MARKER.match(line)
        if m:
            lineno = int(m.group(1)) - 1
            name = m.group(2).encode().decode("unicode_escape")
            if name.startswith("<"):
                current = None
                continue
            path = pathlib.Path(name)
            path = (path if path.is_absolute() else cwd / path).resolve()
            current = (str(path.relative_to(tree))
                       if tree in path.parents else None)
            continue
        lineno += 1
        if current is None:
            continue
        for tok in TOKEN.findall(line):
            out.append((current, lineno, tok))
    return out


def drop_allowed(tokens, rules, side, used):
    """Remove each allowed token sequence that applies to this side."""
    for rule in rules:
        if rule.get("side", "both") not in (side, "both"):
            continue
        if rule.get("system", platform.system()) != platform.system():
            continue
        pattern = TOKEN.findall(rule["drop"])
        n, i, kept = len(pattern), 0, []
        while i < len(tokens):
            if [t[2] for t in tokens[i:i + n]] == pattern:
                used[rule["drop"]] = used.get(rule["drop"], 0) + 1
                i += n
            else:
                kept.append(tokens[i])
                i += 1
        tokens = kept
    return tokens


def as_lines(tokens):
    """Group tokens by source line, for a readable difference listing."""
    lines, key = [], None
    for name, lineno, tok in tokens:
        if (name, lineno) != key:
            key = (name, lineno)
            lines.append([f"{name}:{lineno}:"])
        lines[-1].append(tok)
    return [" ".join(parts) for parts in lines]


def compile_commands(source):
    """The commands with which the configured Makefile compiles `source`."""
    listing = run(["make", "-n", "-B", "static", "shared"], cwd=CONFIGURED)
    commands = []
    for line in listing.stdout.splitlines():
        try:
            words = shlex.split(line)
        except ValueError:
            continue
        if "-c" in words and words and words[-1] == source:
            commands.append(words)
    return commands


def preprocess_as_built(words):
    """Turn a compile command into the matching preprocess command."""
    cmd, skip = [], False
    for w in words:
        if skip:
            skip = False
        elif w == "-o":
            skip = True
        elif w != "-c":
            cmd.append(w)
    return cmd[:-1] + ["-E", cmd[-1]]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--defines", help="verifier flags to use in place of "
                    "ZLIB_DEFINES from proofs/zlib.mk, for experiments")
    args = ap.parse_args()

    conf = settings()
    defines = shlex.split(args.defines if args.defines is not None
                          else conf["ZLIB_DEFINES"])
    sources = conf["ZLIB_VERIFIED"].split()
    rules = (tomllib.loads(ALLOW.read_text()).get("allow", [])
             if ALLOW.exists() else [])
    errors, report, used = [], [], {}

    if not (PATCHED / "zlib.h").exists():
        print("build: ERROR no patched tree; run tools/check_patches.py first")
        return 1

    # ---- configure a copy of the patched tree, as upstream documents ----
    if CONFIGURED.exists():
        shutil.rmtree(CONFIGURED)
    shutil.copytree(PATCHED, CONFIGURED)
    configured = run(["./configure"], cwd=CONFIGURED)
    (BUILD / "configure.log").write_text(configured.stdout + configured.stderr)
    if configured.returncode != 0:
        print("build: ERROR ./configure failed; see build/configure.log")
        return 1
    cc = run(["cc", "--version"]).stdout.splitlines()
    report.append(f"machine: {platform.system()} {platform.machine()}")
    report.append(f"C compiler: {cc[0] if cc else 'unknown'}")
    report.append("verifier flags: " + " ".join(defines)
                  + ("  (overridden on the command line)"
                     if args.defines is not None else ""))

    for source in sources:
        commands = compile_commands(source)
        if len(commands) < 2:
            errors.append(f"{source}: expected a static and a shared compile "
                          f"command, found {len(commands)}")
        verifier_cmd = ["clightgen", "-E", "-I", str(PATCHED), *defines,
                        str(PATCHED / source)]
        seen = run(verifier_cmd)
        if seen.returncode != 0:
            errors.append(f"{source}: clightgen -E failed\n{seen.stderr}")
            continue
        verifier = drop_allowed(tree_tokens(seen.stdout, PATCHED, ROOT),
                                rules, "verifier", used)
        if not verifier:
            errors.append(f"{source}: no tokens from the zlib tree in the "
                          f"verifier's input")
        for words in commands:
            report.append(f"{source}: built by: {' '.join(words)}")
            pre = run(preprocess_as_built(words), cwd=CONFIGURED)
            if pre.returncode != 0:
                errors.append(f"{source}: preprocessing as built failed\n"
                              f"{pre.stderr}")
                continue
            built = drop_allowed(tree_tokens(pre.stdout, CONFIGURED, CONFIGURED),
                                 rules, "build", used)
            files = sorted({t[0] for t in built})
            if [t[2] for t in built] == [t[2] for t in verifier]:
                report.append(f"{source}: SAME, {len(built)} tokens from "
                              f"{', '.join(files)}")
            else:
                diff = list(difflib.unified_diff(
                    as_lines(built), as_lines(verifier), "as built",
                    "as verified", lineterm="", n=0))
                shown = "\n".join(diff[:60])
                more = (f"\n... {len(diff) - 60} more lines"
                        if len(diff) > 60 else "")
                errors.append(f"{source}: the verifier's source differs from "
                              f"what this command compiles:\n  "
                              f"{' '.join(words)}\n{shown}{more}")

    for rule in rules:
        if rule.get("system", platform.system()) != platform.system():
            report.append(f"allowed difference not applicable on this "
                          f"system: {rule['drop']}")
            continue
        report.append(f"allowed difference used {used.get(rule['drop'], 0)} "
                      f"time(s): {rule['drop']}  ({rule['reason']})")
    report.append(f"coverage: {len(sources)} of {len(LIBRARY)} library "
                  f"source files are verified and checked here")

    (BUILD / "build-check.txt").write_text("\n".join(report) + "\n")
    for line in report:
        print(f"build: {line}")
    for e in errors:
        print(f"build: ERROR {e}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
