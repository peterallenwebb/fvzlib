#!/usr/bin/env python3
"""Measure which zlib source files change with the edition of C.

Each of the fifteen library source files is preprocessed with the upstream
build's own command, once under each edition of the C standard and once
under gcc's GNU dialect of each.  The tokens that come from zlib's own
files are compared.  The report says, for each file, which editions give
the same tokens.

This is a measurement, not a check.  It fails only if it cannot run, and
`make full` does not run it.  What it finds depends on the compiler and
the C library, so the record is the run in the toolchain container.

It needs the configured tree that tools/check_build.py makes, so run
`make check build-check` first.

Usage: tools/measure_editions.py
       tools/measure_editions.py --show FILE STD STD

  --show FILE STD STD   print how FILE differs between two editions, for
                        example: --show gzread.c gnu17 gnu23
"""
import argparse
import difflib
import sys

sys.dont_write_bytecode = True
import check_build as cb

ISO = ["c90", "c99", "c11", "c17", "c23"]
GNU = ["gnu90", "gnu99", "gnu11", "gnu17", "gnu23"]


def tokens_under(source, std):
    """The tokens of `source` from zlib's own files under `std`, as
    (file, line, token), or None if it does not preprocess."""
    commands = cb.compile_commands(source)
    if not commands:
        return None
    base = cb.preprocess_as_built(commands[0])
    done = cb.run(base[:1] + [f"-std={std}"] + base[1:], cwd=cb.CONFIGURED)
    if done.returncode != 0:
        return None
    return cb.tree_tokens(done.stdout, cb.CONFIGURED, cb.CONFIGURED)


def groups(source, stds):
    """Partition `stds` by the token sequence each gives for `source`."""
    seen, failed = {}, []
    for std in stds:
        found = tokens_under(source, std)
        if found is None:
            failed.append(std)
        else:
            seen.setdefault(tuple(t for _, _, t in found), []).append(std)
    return list(seen.values()), failed


def show(source, a, b):
    ta, tb = tokens_under(source, a), tokens_under(source, b)
    if ta is None or tb is None:
        print(f"editions: ERROR {source} does not preprocess under both")
        return 1
    diff = list(difflib.unified_diff(cb.as_lines(ta), cb.as_lines(tb),
                                     a, b, lineterm="", n=0))
    for line in diff:
        print(line[:400])
    print(f"editions: {source}: {len(diff)} lines of difference "
          f"between {a} and {b}")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--show", nargs=3, metavar=("FILE", "STD", "STD"))
    args = ap.parse_args()
    if not (cb.CONFIGURED / "Makefile").exists():
        print("editions: ERROR no configured tree; run `make check "
              "build-check` first")
        return 1
    if args.show:
        return show(*args.show)

    cc = cb.run(["cc", "--version"]).stdout.splitlines()
    print(f"editions: C compiler: {cc[0] if cc else 'unknown'}")
    print(f"editions: compared: {' '.join(ISO)} and {' '.join(GNU)}")
    same_all, same_iso, errors = 0, 0, 0
    for name in cb.LIBRARY:
        source = f"{name}.c"
        every, failed = groups(source, ISO + GNU)
        iso, _ = groups(source, ISO)
        if failed:
            errors += 1
            print(f"editions: ERROR {source} does not preprocess under "
                  + " ".join(failed))
            continue
        same_all += len(every) == 1
        same_iso += len(iso) == 1
        if len(every) == 1:
            print(f"editions: {source}: the same under every one")
        else:
            print(f"editions: {source}: {len(every)} forms: "
                  + "; ".join(" ".join(g) for g in every))
    total = len(cb.LIBRARY)
    print(f"editions: {same_all} of {total} files are the same under every "
          f"edition and dialect, {same_iso} under every ISO edition")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
