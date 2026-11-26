# Moving the work to x86-64 Linux

The project's first target is zlib 1.4 on x86-64 Linux. Until now every
proof has been checked on an ARM Mac, where the results are exploratory.
This note says how to run the work on the target and what to expect.

The target environment is a container. The reasons are in the README, under
"The build environment: a container". The host machine needs only git and
Podman.

## Steps

1. **Get the repository, with the pinned zlib.**

   ```
   git clone --recurse-submodules <repository URL> fvzlib
   ```

   In an existing clone, `git submodule update --init` fetches zlib.

2. **Install Podman.** On Debian or Ubuntu:

   ```
   sudo apt install podman
   ```

   Podman runs the container as the ordinary user. No daemon and no group
   membership is needed.

3. **Check everything.**

   ```
   tools/in-container.sh make full
   ```

   The first run builds the toolchain image from `env/Containerfile`. It
   compiles OCaml, Rocq, CompCert, and VST from source. That took about
   fifteen minutes on a 16-core machine and 31 minutes on a hosted runner
   with 4 processors. Later runs reuse the image, and `make full` then takes about five
   minutes.

   `make full` is the one command behind Milestone 1's first two exit
   criteria. It runs, in order:

   | Step | What it checks |
   |---|---|
   | `env-check` | Every pinned package is installed at its pinned version, and the machine and CompCert are x86-64 Linux |
   | `check` | The specifications, test vectors, layer rules, assumption audit, traceability, the patch sequence with its witnesses, and the review of preconditions |
   | `build-check` | The source given to the verifier is, token for token, the source the upstream build compiles |
   | `differential` | zlib as gcc builds it, pristine and patched, returns what the Adler-32 reference model says, on about five thousand inputs |
   | `proofs` | Every VST proof for `adler32.c` |
   | `spikes` | The contract transfer and termination spikes |
   | `claim` | The commit, patch, flags, theorem, axioms, functions, and ledger entries that the claim for `adler32.c` names are the ones the build uses |

Other uses of the script:

| Command | What it does |
|---|---|
| `tools/in-container.sh` | Opens a shell in the container |
| `tools/in-container.sh make check` | Runs any one command there |
| `tools/in-container.sh --build` | Builds the image if needed and prints its name |

The repository is mounted in the container at `/fvzlib`. Files are edited on
the host as usual, and build products appear in the host's working tree.

## What the first run found

The move was made on 2026-11-25, on an x86-64 machine running Ubuntu 26.04
with Podman 5.7. `make full` now passes in the container from a clean tree.
The first run stopped twice.

- **The image built at the first attempt.**
- **`build-check` reported one difference.** The flags in `proofs/zlib.mk`
  were a prediction of what the upstream `./configure` chooses on Linux,
  and the prediction was right. The one difference was the symbol
  visibility attribute on two declarations in `zutil.h`. CompCert undefines
  `__GNUC__` when it preprocesses, and the C library then defines
  `__attribute__` away. The same difference was already accepted on macOS,
  where it has another cause. It is now also accepted on Linux, in
  `env/build-check-allow.toml`, with its reason.
- **Every proof carried over.** No proof script changed.
- **Two files named CompCert built-in functions that exist only on ARM.**
  The guarded combine proof and the ticked spike each keep a list of names
  that a computation must leave folded. The lists now hold only the
  identifiers of the source file. The computed syntax trees did not need
  regenerating.

Two checks that the README said must be repeated on the target were also
run. The results are in the README, under "Toolchain versions" and "C
standard editions".

- **CompCert's front end translates all fifteen library source files.**
- **The comparison across C editions gives a new result.** On Linux,
  `gzread.c` differs under the 2023 edition, which gcc 15 uses by default.

## Moving a pin

The image's tag is a hash of `env/Containerfile`, `env/packages.lock`, and
`tools/bootstrap.sh`. Changing any of them makes the next run of
`tools/in-container.sh` build a new image. Old images stay until removed
with `podman image rm`.

## Without a container

`tools/bootstrap.sh` installs the same opam packages into an opam switch on
the machine itself. It needs opam, git, make, gcc, m4, patch, pkg-config,
Python 3.11 or later, and the GMP development files, and it says what is
missing. Then:

```
opam exec --switch=fvzlib -- make full
```

This route does not pin the system packages or the opam build recipes. Its
results are a convenience. The results that count for the first target are
those from the container.

## What does not travel with the repository

The assistant's working notes live outside the repository, on the Mac. The
README records every decision, so nothing essential is lost, but a session
on the Linux machine starts without those notes. To carry them over, copy
the directory `~/.claude/projects/-Users-webbpa-Code-fvzlib/memory/` to the
matching project directory on the Linux machine.

## Limits of the pinning

- **Building the image depends on outside services.** These are the image
  registry, the Ubuntu snapshot service, GitHub, and the sites that opam
  downloads source archives from. opam checks each archive against a
  checksum.
- **Two builds of the image give the same versions, not the same bytes.**
- **The built image is not published.** Each person builds their own.
- **The image has been built twice, on the same day**, on two machines:
  the development laptop and a hosted runner in continuous integration.
  Both gave the same versions and the same results. That does not yet show
  the image can still be built once the outside services have moved on.
- **`make full` records what it ran on** in `build/environment.txt`: the
  image, its pins, and the compiler version.
