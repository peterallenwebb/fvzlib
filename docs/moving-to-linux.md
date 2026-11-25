# Moving the work to the x86-64 Linux machine

The project's first target is zlib 1.4 on x86-64 Linux. Until now every
proof has been checked on an ARM Mac, where the results are exploratory.
This note says how to set up the Linux machine and what to expect.

## Steps

1. **Get the repository onto the machine.** The repository has no remote
   yet. Either push it to a private remote and clone from there, or copy it
   across with a git bundle:

   ```
   git bundle create fvzlib.bundle --all
   ```

   On the Linux machine, `git clone fvzlib.bundle fvzlib`.

2. **Install the system tools.** The setup script needs opam, git, make,
   gcc, m4, patch, pkg-config, Python 3.11 or later, and the GMP development
   files. On Debian or Ubuntu:

   ```
   sudo apt install opam git make gcc m4 patch python3 pkg-config libgmp-dev
   ```

   If opam has never been used by this user, run `opam init` once.

3. **Install the pinned toolchain.**

   ```
   tools/bootstrap.sh
   ```

   This fetches the pinned upstream zlib, creates an opam switch named
   `fvzlib`, and installs the exact package versions listed in
   `env/packages.lock`. It compiles OCaml, Rocq, CompCert, and VST from
   source, so the first run takes from fifteen minutes to an hour. It can be
   run again safely.

4. **Check everything.**

   ```
   opam exec --switch=fvzlib -- make full
   ```

   This is the one command behind Milestone 1's first two exit criteria. It
   runs, in order:

   | Step | What it checks |
   |---|---|
   | `env-check` | Every pinned package is installed at its pinned version, and the machine and CompCert are x86-64 Linux |
   | `check` | The specifications, test vectors, layer rules, assumption audit, traceability, and the patch sequence with its witnesses |
   | `build-check` | The source given to the verifier is, token for token, the source the upstream build compiles |
   | `proofs` | Every VST proof for `adler32.c` |
   | `spikes` | The contract transfer and termination spikes |

## What to expect

Some steps may fail on the first run. Each failure tells us something we
need to know, and none can be seen from the Mac.

- **`build-check` is the most likely to report something.** On Linux the
  upstream `./configure` makes choices it does not make on the Mac. In
  particular it turns on the 64-bit file offset interface. The flags in
  `proofs/zlib.mk` are our prediction of its choices for Linux. This run is
  the first real test of that prediction. A difference is printed as the
  lines of code that differ.
- **The proofs may need small repairs.** They are about the Clight that
  CompCert generates for the local target. The C types involved are the same
  on both machines, so we expect the proofs to carry over, but that is a
  prediction too.
- **Files that pin a syntax tree may need regenerating.** The spikes and the
  guarded combine proof each hold a transformed copy of a function. If
  CompCert names a temporary differently on x86-64, those copies will no
  longer match and must be regenerated.

## What does not travel with the repository

The assistant's working notes live outside the repository, on the Mac. The
README records every decision, so nothing essential is lost, but a session
on the Linux machine starts without those notes. To carry them over, copy
the directory `~/.claude/projects/-Users-webbpa-Code-fvzlib/memory/` to the
matching project directory on the Linux machine.

## Limits of the pinning

- The lock file pins the version of every opam package. opam checks each
  source archive against a checksum. The opam repositories themselves are
  not pinned to a commit, so a package's build recipe could in principle
  change under the same version number.
- System packages are not pinned: the C compiler that preprocesses for
  CompCert, the C library headers, and GMP. `make full` records the compiler
  version in `build/environment.txt`.
