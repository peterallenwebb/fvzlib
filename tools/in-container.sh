#!/bin/sh
# Run a command inside the fvzlib toolchain container.
#
#   tools/in-container.sh make full     check everything
#   tools/in-container.sh               open a shell
#   tools/in-container.sh --build       only build the image
#
# The container is x86-64 Linux with the pinned toolchain, defined by
# env/Containerfile.  This repository is mounted in it at /fvzlib, so the
# command sees the files as they are here and writes its results here.  The
# command runs inside the project's opam switch.
#
# The image is built on first use, which takes from fifteen minutes to an
# hour.  Its tag is a hash of the files that define it.  When a pin changes,
# the tag changes and the image is built again.
#
# Needs Podman, running without root.  Nothing else is needed on the host.
#
# Environment:
#   FVZLIB_IMAGE   use this image instead of building one

set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
INPUTS="env/Containerfile env/packages.lock tools/bootstrap.sh"

die() { printf 'in-container: ERROR %s\n' "$*" >&2; exit 1; }

command -v podman >/dev/null 2>&1 ||
    die "podman was not found.  On Debian or Ubuntu: sudo apt install podman"

if [ -n "${FVZLIB_IMAGE:-}" ]; then
    IMAGE=$FVZLIB_IMAGE
else
    # shellcheck disable=SC2086
    TAG=$(cd "$ROOT" && cat $INPUTS | sha256sum | cut -c1-12)
    IMAGE=localhost/fvzlib-toolchain:$TAG
    if ! podman image exists "$IMAGE"; then
        printf 'in-container: building %s\n' "$IMAGE" >&2
        podman build --platform linux/amd64 --tag "$IMAGE" \
            --file "$ROOT/env/Containerfile" "$ROOT" >&2
    fi
fi

if [ "${1:-}" = --build ]; then
    printf '%s\n' "$IMAGE"
    exit 0
fi

# A terminal only when there is one, so the script also works in a pipeline.
TTY=""
if [ -t 0 ] && [ -t 1 ]; then TTY="--tty"; fi

# keep-id makes the invoking user the image's user 1000, so files written in
# the mounted repository belong to the invoking user.
# shellcheck disable=SC2086
exec podman run --rm --interactive $TTY \
    --platform linux/amd64 \
    --userns=keep-id:uid=1000,gid=1000 \
    --security-opt label=disable \
    --volume "$ROOT:/fvzlib" \
    --workdir /fvzlib \
    --env FVZLIB_IMAGE="$IMAGE" \
    "$IMAGE" "$@"
