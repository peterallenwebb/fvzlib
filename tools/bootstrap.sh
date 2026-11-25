#!/bin/sh
# Set up the pinned fvzlib toolchain.
#
#   tools/bootstrap.sh
#   tools/bootstrap.sh --toolchain-only
#
# Creates an opam switch, by default named `fvzlib`, and installs into it the
# exact package versions listed in env/packages.lock.  It is safe to run
# again: an existing switch is kept and only missing packages are installed.
# It installs nothing outside opam and never asks for a password.  If a
# system package is missing it says which one and stops.
#
# The first run compiles OCaml, Rocq, CompCert, and VST from source, which
# takes from fifteen minutes to an hour.
#
# With --toolchain-only it needs only itself and env/packages.lock.  It does
# not fetch upstream zlib and does not run the final check.  env/Containerfile
# uses this to build the toolchain image, where the repository is absent.
#
# Environment:
#   FVZLIB_SWITCH   name of the opam switch (default: fvzlib)

set -eu

TOOLCHAIN_ONLY=""
case "${1:-}" in
    "") ;;
    --toolchain-only) TOOLCHAIN_ONLY=yes ;;
    *) printf 'usage: tools/bootstrap.sh [--toolchain-only]\n' >&2; exit 2 ;;
esac

ROOT=$(cd "$(dirname "$0")/.." && pwd)
SWITCH=${FVZLIB_SWITCH:-fvzlib}
LOCK="$ROOT/env/packages.lock"
OCAML=$(grep '^ocaml-base-compiler\.' "$LOCK")
ROCQ_REPO=https://coq.inria.fr/opam/released

say() { printf 'bootstrap: %s\n' "$*"; }
die() { printf 'bootstrap: ERROR %s\n' "$*" >&2; exit 1; }

# ---- system prerequisites -------------------------------------------------

missing=""
for tool in opam git make gcc m4 patch python3 pkg-config; do
    command -v "$tool" >/dev/null 2>&1 || missing="$missing $tool"
done
# On macOS the system compiler is clang under the name cc; gcc is not needed.
if [ "$(uname -s)" = Darwin ]; then
    missing=$(printf '%s' "$missing" | sed 's/ gcc//')
fi
if [ -n "$missing" ]; then
    say "missing system tools:$missing"
    say "on Debian or Ubuntu:  sudo apt install opam git make gcc m4 patch python3 pkg-config libgmp-dev"
    say "on Fedora:            sudo dnf install opam git make gcc m4 patch python3 pkgconf gmp-devel"
    die "install them and run this script again"
fi

python3 - <<'EOF' || die "python3 must be version 3.11 or later"
import sys
sys.exit(0 if sys.version_info >= (3, 11) else 1)
EOF

if ! pkg-config --exists gmp 2>/dev/null && [ "$(uname -s)" != Darwin ]; then
    say "the GMP development files were not found"
    say "on Debian or Ubuntu:  sudo apt install libgmp-dev"
    say "on Fedora:            sudo dnf install gmp-devel"
    die "install them and run this script again"
fi

if [ ! -d "${OPAMROOT:-$HOME/.opam}" ]; then
    say "opam has not been set up for this user"
    die "run 'opam init' once, then run this script again"
fi

# ---- upstream source ------------------------------------------------------

if [ -z "$TOOLCHAIN_ONLY" ] && [ ! -f "$ROOT/upstream/zlib/zlib.h" ]; then
    say "fetching the pinned upstream zlib"
    git -C "$ROOT" submodule update --init
fi

# ---- the switch -----------------------------------------------------------

if opam switch list --short | grep -qx "$SWITCH"; then
    say "using the existing switch $SWITCH"
else
    say "creating the switch $SWITCH with $OCAML"
    opam switch create "$SWITCH" "$OCAML" --no-switch --yes
fi

if ! opam repository list --switch="$SWITCH" --short | grep -qx coq-released; then
    say "adding the Rocq package repository"
    opam repository add coq-released "$ROCQ_REPO" --switch="$SWITCH" --yes
fi

say "installing the pinned packages"
# shellcheck disable=SC2046
opam install --switch="$SWITCH" --yes $(tr '\n' ' ' < "$LOCK")

# ---- confirm --------------------------------------------------------------

if [ -n "$TOOLCHAIN_ONLY" ]; then
    say "done.  The toolchain is installed in the switch $SWITCH."
    exit 0
fi

opam exec --switch="$SWITCH" -- python3 "$ROOT/tools/check_env.py" --exploratory

say "done.  To check everything, run:"
say "  opam exec --switch=$SWITCH -- make full"
