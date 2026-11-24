# fvzlib

A formal verification effort for [zlib](https://zlib.net).

## Goal

Produce either a world-class demonstration that zlib is correct, safe, and
secure, or a set of patches that bring it to that state.

No demonstration can be absolute. "Correct" here always means correct relative
to a specification, a set of build configurations, and a trusted base. The
objectives below exist to make those three things explicit, small, and
independently checkable.

## Status

Objectives are set as a starting point, and the high-level decisions are
made. See [Decisions](#decisions), [Milestones](#milestones), and
[Open decisions](#open-decisions).

Work on Milestone 1 has started. The format specification and the API
behavior model for Adler-32 exist, with their traceability file. No C proof
work has started. One finding about zlib 1.4 is recorded in the ledger and
resolved by the first patch in the patch sequence.

## What is in the repository

| Path | Contents |
|---|---|
| `spec/format/` | Layer 1. Format specifications. Standard library only. |
| `spec/api/` | Layer 2. API behavior. Depends on Layer 1 only. |
| `audit/` | Lists of results that must depend on no axioms |
| `trace/` | Traceability from source sentences to definitions and theorems |
| `ledger/` | Findings about zlib, one file each |
| `upstream/zlib/` | Pristine zlib 1.4, a git submodule pinned to the release commit |
| `patches/` | The patch sequence: one file per patch, and the `sequence` file that orders them |
| `tests/witness/` | Programs that fail on pristine zlib and pass once patched |
| `references/` | Source documents, unmodified |
| `tools/` | Checks run by the build |
| `build/` | Generated. Holds the pristine and patched trees. Not committed. |

In `spec/`, a file named after a topic holds definitions only and is trusted
reading. Its `Facts` and `Tests` companions hold evidence and need not be
read to know what is claimed.

This layout is provisional until the last open decision is settled.

To build and check, with the pinned toolchain active and a C compiler
available:

```
git submodule update --init
make check
```

That compiles the Rocq sources, which runs the test vectors. It then checks
the layer dependency rules, the assumption audit, and traceability against
RFC 1950 and the pinned `zlib.h`. Last, it applies the patch sequence to a
copy of upstream and runs each witness against both trees.

The patch sequence currently holds one patch.

## Guiding principles

The first four are the reason the project exists. The rest support them.

1. **No vulnerabilities for dependents.** Maintainers who depend on zlib should
   have the highest possible confidence that using it introduces no
   vulnerability of any kind.
2. **It does what is claimed.** They should have the highest possible
   confidence that the code does what is claimed, and that new releases do not
   break that claimed behavior.
3. **Bounded work.** Every function call terminates after a well-characterized
   number of operations.
4. **Releases are checkable.** New releases of zlib can be checked for
   regressions against these criteria.
5. **The trusted base is explicit.** Every guarantee rests on something
   unproven: the proof checker, the C semantics, the platform ABI, the
   specification text. We enumerate these and keep the list short.
6. **The specification is the primary product.** A proof against a vague or
   wrong specification is worth nothing. Specifications are short, readable by
   a zlib maintainer who is not a proof engineer, and stated in terms of byte
   sequences.
7. **Correctness is defined by the documents, not by the implementation.** The
   zlib manual (`zlib.h`) and RFCs 1950, 1951, and 1952 define correct
   behavior. Where the code and the documents disagree, we decide consciously
   and record the decision.
8. **Guarantees hold under ISO C.** Dependents build with many compilers. A
   property that holds only under one verifier's C semantics is not enough.
9. **Every input is adversarial.** Preconditions may constrain only what the
   caller controls, such as a valid stream structure and buffers of the stated
   size. They never constrain data content.
10. **Every resource is bounded.** Time, memory allocated, allocator calls,
    stack depth, and output per call are each bounded by a stated function of
    documented parameters.
11. **Claims are honest.** We never claim more than is proven. Limits are
    stated as prominently as results.
12. **Change is local.** Proofs are modular, so a change to one function
    requires re-proving that function and little else.
13. **Specifications are a consumer artifact.** A downstream project doing its
    own verification can import our function contracts.

## How we will work

These objectives are ambitious, and we will not attempt them end to end from
the start.

- **Incremental value.** Each step must deliver knowledge or a usable result on
  its own. A partial result that is honest about its scope is a success.
- **Common builds first.** We begin with the build options most commonly used
  in release builds, on the most widely deployed platform, and widen from
  there.
- **Verify what ships.** We do not verify a configuration that is easier to
  prove but that nobody runs.
- **Demonstrate first, upstream later.** We do not expect upstream appetite
  without a complete product and considerable trust building. The first target
  is a demonstration on a patched copy of the most recent zlib release. Patches
  are kept upstream-ready but are not submitted officially until that
  demonstration exists.
- **Every line accounted for.** Each function ends in exactly one of three
  states: proven as is, proven after a named patch, or excluded with a stated
  reason. That table is both the progress tracker and the final result.

## Objectives

### The claim

- **One headline claim.** A single sentence a dependent can quote, naming the
  zlib release, the configurations, and the limits.
- **One top-level theorem.** The claim is backed by a single linked theorem
  with its assumptions printed, not by per-function proofs joined by unchecked
  glue.

### Subject and scope

- **Upstream source, verbatim.** The subject is the most recent upstream zlib
  release, pinned by tag and hash. Every deviation from it is a named patch.
- **The library proper.** Scope is the code that compiles into the zlib
  library and the API in `zlib.h`. The `contrib` directory, including minizip,
  is out of scope and we say so prominently.
- **A configuration matrix.** Coverage is declared per cell of a matrix of
  build options, data models, and byte orders. The first cell is the most
  common release build.
- **Inflate first.** Decompression of untrusted input is the main attack
  surface and takes priority over compression.
- **Proven equals built.** A mechanical check ties the preprocessed source
  given to the verifier to what the official build compiles.

### Safety and security

- **Memory safety.** No out-of-bounds access, use after free, null
  dereference, or read of uninitialized memory, for every exported function
  under its documented preconditions.
- **No undefined behavior under ISO C.** Each difference between the
  verifier's C semantics and ISO C is enumerated and closed by a proof, a
  second tool, or a patch. Known candidates are shifts of negative values,
  aliasing, implementation-defined conversions, and evaluation order.
- **A written threat model.** The attacker may control compressed input,
  plaintext, every integer parameter, gzip header fields, and allocator
  failure at any call.
- **Minimal preconditions.** Each precondition is reviewed for being necessary
  and checkable by the caller.
- **No leaks.** Every path, including every error path, releases what it
  allocated.
- **Stream independence.** Operations on distinct streams do not interfere,
  which is the basis of the library's thread-safety claim.
- **Output depends only on input.** Output is a function of the input,
  parameters, and call sequence. No unrelated or uninitialized memory can
  reach it.
- **Historical CVEs.** Every past zlib CVE becomes a regression test, and each
  memory-safety CVE becomes a stated corollary of the proofs.

### Functional correctness

- **Reference models.** Executable models of Deflate, the zlib and gzip
  wrappers, CRC-32, and Adler-32, validated against RFC test vectors and
  differentially against upstream.
- **Inflate.** Inflate produces exactly what the model decodes, or reports a
  data error.
- **A precise acceptance set.** The model defines exactly which byte streams
  inflate accepts, including its documented leniencies.
- **Deflate.** Deflate output is format-valid and inflates to the input.
- **Bounds.** The output bound functions are sound.
- **Chunking independence.** Results do not depend on how the caller splits
  input and output across calls, except where the manual says they do.
- **Documented modes.** Flush modes, strategies, levels, and dictionary
  functions behave as the manual states.
- **Checksums.** The checksum functions equal their mathematical definitions.
- **Determinism.** Output is deterministic within a release. Byte-stable
  output across releases is tested, not proven.

### Termination and cost

- **Termination.** Every exported function terminates on every input. There
  is no recursion.
- **A defined cost unit.** "Number of operations" has one fixed, formal
  meaning across the project.
- **Per-call bounds.** Each exported function has a proven cost bound in terms
  of input length, output space, and documented parameters.
- **Streaming progress.** Each streaming call consumes input, produces output,
  or reports that it cannot, so a correct caller loop terminates on finite
  input.
- **Space bounds.** Allocation and stack depth have proven bounds.

### Specification validation

- **Traceability.** Every normative sentence in `zlib.h` and the three RFCs
  maps to a theorem, a test, or an explicit "not covered" entry.
- **Mutation testing.** Reintroducing each historical CVE, and random
  mutations of the source, must make a proof fail. This guards against vacuous
  specifications.
- **A verified client.** zlib's own canonical usage example is proven to
  round-trip any input, showing the specifications are strong enough to build
  on.
- **Informal arguments become theorems.** Safety margins that upstream
  justifies in comments or by separate programs are proven. Examples are the
  decoding table size bound, the shared buffer layout in deflate, and the
  margins of the fast inflate loop.

### Findings and patches

- **A findings ledger.** Every failed proof attempt resolves into a defect
  with a witness input, an undocumented precondition, or a tool limit.
- **Three patch classes.** Defect fixes, hardening that removes undefined
  behavior, and restructuring done only for provability. The third class is
  kept minimal and each such patch carries an equivalence argument.
- **Documentation patches count.** Making an implicit precondition explicit in
  the manual is a valid result.
- **Upstream-ready patches.** Patches follow upstream style and portability
  rules and come with benchmarks showing no regression, so they can be
  submitted once the demonstration is complete.
- **Responsible disclosure.** A finding with security impact on released zlib
  is reported privately to the zlib maintainer before it is made public. This
  is separate from, and not deferred with, official patch submission.

### Evidence, reproducibility, and review

- **Machine-checked proofs.** Proofs are checked by a small trusted kernel,
  with no admitted lemmas or project-specific axioms beyond a published list.
- **Independent evidence.** A second tool with a different trusted base checks
  the same source. The verified source is fuzzed differentially against the
  reference models. Of all the objectives, this has the lowest priority.
- **Named assumptions.** The C library functions zlib calls, and any
  operating system or instruction behavior we rely on, are listed as named
  assumptions.
- **Reproducibility.** The whole result rebuilds from an archived, pinned
  environment with one command.
- **External review.** The specifications are reviewed by a zlib expert and a
  verification expert.
- **Prior art.** A survey positions this work against existing verified
  compression efforts. A first pass is under [Related work](#related-work).
- **A reusable specification layer.** Models and specifications are
  independent of the implementation, so other Deflate libraries can be checked
  against them.

### Regression checking

- **Verification is a gate.** Continuous integration rechecks every proof from
  a clean environment and compares the assumption list against an allowed set.
- **Status per upstream tag.** Each upstream release gets a published
  verification status.
- **An intake procedure.** A written procedure takes a new upstream release
  through diffing, re-proving changed functions, and rerunning the test
  suites. Time to re-verify is tracked.
- **Specification changes are behavior changes.** A release either states that
  the specification is unchanged or lists what changed.

### Non-goals

- Compression-ratio side channels, which are inherent to compression.
- Code outside the library proper, including `contrib`.
- Other zlib-compatible implementations, although the specification layer
  should be reusable for them.
- A guarantee about binaries from unverified compilers beyond what freedom
  from undefined behavior under ISO C provides.

## Known risks and limits

- **Termination and cost.** Mainstream separation logic tools for C prove
  partial correctness only. Our approach is tick instrumentation, described
  under Decisions, and it is untested until the Adler-32 spike is run.
- **Hard limits.** Inline assembly, variadic formatted output in the file
  layer, and operating system I/O can at best be handled through small
  axiomatized models. The headline claim must name them.
- **Provability patches.** If upstream never accepts them, the result is a
  demonstration about a patched zlib. We accept that as the first target.
- **Scale.** The full objective set is large. The incremental approach above
  is the mitigation.

## Decisions

### Primary toolchain: VST with CompCert

Decided 2026-11-23.

The primary proofs are written in the Verified Software Toolchain (VST), in
the Rocq prover, against CompCert's Clight semantics. We use the stable VST
2.x line. The 3.x line, built on Iris, is still in beta and will be revisited
when it is released. Exact versions are given under "Toolchain versions"
below.

Why:

- The proofs are foundational. VST's program logic is itself proven sound
  against CompCert's operational semantics, and CompCert's correctness theorem
  extends the result to machine code.
- VST has been used to verify deployed C code of a similar character, with
  byte buffers, bit manipulation, and tight loops.
- Its function contracts can be imported by downstream verification projects.
- No alternative offers the same combination. In particular, no Lean tool for
  C verification is mature, and Lean has no verified C compiler.

Consequences we accept, each confirmed against the installed VST and the
upstream source:

- **No goto.** VST can prove a goto statement only when it is unreachable.
  Upstream `inflate`, the fast inflate loop, and `inflateBack` use goto. See
  the decision on provability transformations below.
- **Partial correctness only.** Termination and cost bounds need a
  supplementary method.
- **One target's choices per proof.** CompCert fixes every
  implementation-defined choice for a given target, and Clight fixes one
  evaluation order. See the policy below.
- **No inline assembly.** The ARM CRC path cannot be proven at the C level.
- **Target coverage.** CompCert targets are LP64 or ILP32. The 64-bit Windows
  data model is out of reach for the primary proofs.
- **Licensing.** CompCert is licensed for non-commercial use, with commercial
  licenses sold by AbsInt. The parts VST depends on are also available under
  the LGPL, so the proofs can be reproduced freely. Most dependents will build
  with other compilers, so the ISO C argument below is the main route by which
  the proofs deliver value to them.

### Toolchain versions

Decided 2026-11-24.

| Tool | Version |
|---|---|
| Rocq | 9.2.0 |
| CompCert | 3.18 |
| VST | 2.17 |
| OCaml | 4.14.3 |

All are installed from opam, using the default repository and the
`coq-released` repository. The same versions are used on every machine.

Why these:

- This is the newest set that works together. Rocq 9.3.0 exists, but the
  CompCert 3.18 package does not accept it yet.
- CompCert 3.18 changed its formal semantics. Loads and stores carry an
  explicit check on address offsets, the memory model handles alignment per
  target, and the semantics of `free` is stricter. VST 2.17 adapts to this.
  Proofs written against an older release would rest on an older definition
  of the language.
- CompCert 3.17 and 3.18 fixed front-end bugs, including one in how switch
  statements are elaborated, and 3.18 fixed a jump table instruction on
  x86-64.

Known quirk: the CompCert 3.18 release reports itself as version 3.17. Its
`VERSION` file was not updated upstream. The installed sources do contain the
3.18 semantic changes. We therefore identify CompCert by its opam package
version and source hash, never by the output of `ccomp -version`.

Checked on an ARM Mac with these versions: a small C function was translated,
a VST contract for it was proven, and the assumption list was the standard
classical set. All fifteen library source files of zlib 1.4 were translated
by the CompCert front end, with the ARM CRC path disabled. Both checks must
be repeated on the x86-64 Linux target.

### Policy on undefined, implementation-defined, and unspecified behavior

Decided 2026-11-23.

- **Undefined behavior.** We identify every instance we can find in zlib and
  patch it where that is reasonable. VST already rules out signed overflow,
  out-of-range shift amounts, division errors, invalid pointer use, and use of
  uninitialized values. The residue, which includes shifts of negative values
  and violations of the aliasing rules, is handled as described under
  "Closing the undefined behavior gap, and secondary tools" below.
- **Implementation-defined and unspecified behavior.** We accept reliance on
  it only where we can show that every behavior permitted by the C standard
  meets our specification. In practice that means one of two things: showing
  that the code never exercises the behavior, or, for parameters such as type
  widths and byte order, re-checking the proofs for each supported target and
  declaring the result per matrix cell.
- **Evaluation order.** A check establishes that no expression's value depends
  on the order in which its operands are evaluated. This check needs a
  secondary tool, so it is low priority and stays open until then.
- **The resulting claim.** "Holds for any conforming compiler" is not a single
  VST theorem. It is a VST theorem together with a checked argument that zlib
  stays inside the fragment of C where CompCert's semantics and the standard
  agree.

### Provability transformations, starting with goto

Decided 2026-11-23.

Where VST cannot express a construct that upstream uses, we do not patch the C
source by hand. We transform the program in the Clight syntax tree that the
proofs are written against, and we leave the upstream source untouched.

- **Mechanical and minimal.** Each transformation is computed by a small,
  auditable Rocq function. It is never a free-form rewrite.
- **Equivalence is an explicit obligation.** Each transformation has a ledger
  entry stating that it preserves behavior. The entry is either proven, by one
  theorem covering every function the transformation applies to, or listed as
  an assumption in the headline claim. Work may proceed while an entry is
  unproven.
- **Source patches are the fallback.** If a transformation cannot be made to
  work, we fall back to a provability patch on the C source, knowingly, with
  its own equivalence argument. Such a patch joins the patch sequence.

Why:

- The shipped code stays the original, so theorems apply to what dependents
  actually run, there is no performance question, and nothing depends on
  upstream accepting a patch.
- A transformation reapplies to each new upstream release with no rebasing and
  no new equivalence proof.
- Keeping restructuring out of the source diff lets the findings ledger say
  "zlib is correct except for these named defects".
- Goto is the first case of a category. This rule covers the later cases.

What we measured, on the 1.4 release tag with the default configuration: goto
appears only in `inflate.c`, `infback.c`, and `inffast.c`. The other twelve
library source files contain none.

| File | Goto statements written | After macro expansion | Pattern |
|---|---|---|---|
| `inflate.c` | 15 | 37 | Forward jump to one cleanup label at the end of the function |
| `infback.c` | 5 | 21 | Forward jump to one cleanup label at the end of the function |
| `inffast.c` | 2 | 2 | Backward jumps that form loops |

Planned treatment:

- **Forward jumps to the cleanup label.** Replace each jump with a copy of the
  code at the label. This is valid because the label is at the end of the
  function and the code after it always returns. It is also the shape with the
  simplest behavior-preservation proof.
- **Backward jumps in the fast loop.** These need separate treatment, since
  copying the target does not work for a jump backward. Not yet designed.

Known risk: VST proves a contract for the transformed function, and we want
that contract for the original. Carrying it across may require working inside
VST's soundness proof. A whole-program statement would be weaker, because it
loses the per-function contract that downstream projects would import. A
spike on a toy function must settle this before we rely on the approach.

### First target

Decided 2026-11-23.

| Part | Choice |
|---|---|
| Release | zlib 1.4, tag `v1.4`, commit `99623ef7097352da7993ba614161fd6a311e046e`, dated 4 November 2026 |
| Build options | Upstream `./configure` defaults with no extra defines |
| Platform | x86-64 Linux |
| Data model | LP64, little-endian |

This is the first cell of the configuration matrix. Planned later cells, in
order:

1. **ARM Linux, same options.** A baseline ARM Linux build does not enable
   the inline assembly CRC path, so it should compile the same zlib code.
   Expected to be nearly free.
2. **Debian and Ubuntu on x86.** Their packaging adds `-DUNALIGNED_OK`, which
   makes the deflate match finder read 16-bit values through cast pointers.
   It affects deflate only and is a likely finding under the undefined
   behavior policy.
3. **macOS on ARM.** Apple's compiler enables the inline assembly CRC path,
   which needs an instruction-level model.

Why:

- 1.4 is the most recent release and is already shipped by Alpine, Arch, and
  Homebrew. Debian and Ubuntu were still on 1.3.x when we checked.
- 1.4 is a security release. Its changelog lists about a dozen memory-safety
  fixes across inflate, deflate, and the file layer. Each one is a ready-made
  case for mutation testing.
- The upstream defaults are what Alpine, Arch, and Homebrew build, and they
  are the baseline every other distribution modifies.
- x86-64 Linux is the most widely deployed platform for upstream zlib, and no
  code path on it uses assembly.
- CompCert's front end, at versions 3.16 and 3.18, translated all fifteen
  library source files of 1.4 in this configuration. The check was run on an ARM Mac
  with the ARM CRC path disabled, so it must be repeated on the real target.

Consequences:

- **The work moves to an x86-64 Linux machine** before proof work begins. The
  toolchain is installed there for the x86-64 Linux target, and the Clight
  syntax trees are generated against that machine's system headers.
- **"Proven equals built" has real work to do.** CompCert reports the 1999
  standard version and current gcc reports a later one. zlib tests that value
  in three headers. In the default configuration the affected code appears
  inactive, and the mechanical check must confirm it.
- **Fedora is not covered.** It ships zlib-ng in compatibility mode, which is
  a different codebase.
- **Optimization level is not part of the cell.** The proofs concern the
  source. Distributions vary between `-O2` and `-O3`.

### Termination and cost: tick instrumentation

Decided 2026-11-23.

VST proves that a program never gets stuck, for any number of steps. A program
that loops forever satisfies that, so VST alone says nothing about
termination. We therefore treat termination as a safety property.

- **Instrument.** A small Rocq function adds a counter to the Clight syntax
  tree. The counter is decremented at every loop iteration, every backward
  jump, and every function entry. If it would go below zero, the program takes
  a step that VST can only prove unreachable.
- **Prove safety.** Each function contract gains a cost clause. The caller
  supplies a counter at least as large as a stated bound, and the function
  returns what is left. An ordinary VST proof shows the counter never runs
  out.
- **Conclude termination.** One generic theorem says a program whose ticks are
  bounded must terminate. A second says that removing the counter does not
  change behavior.

This is a provability transformation under the rule above. It adds two ledger
entries, bounded ticks imply termination and erasure preserves behavior, and
it shares the open risk about carrying a contract back to the original code.

**The cost unit** is the number of loop iterations and function calls of the
source program. It is a property of the source, so it means the same thing
under any compiler. It bounds machine steps up to a constant, because only a
bounded amount of straight-line code separates two ticks.

How contracts state cost:

- **Bounds are amortized.** Some work is deferred between calls. Deflate, for
  example, slides its window occasionally and carries pending output. A
  per-call bound has a potential term on the stream's abstract state, plus
  terms linear in input consumed and output produced.
- **Library calls are charged by size.** A copy of a given length costs that
  many ticks, added mechanically before the call.
- **Caller-supplied allocators are assumed to terminate.** The assumption is
  named in the headline claim, and each call is charged one tick.
- **Deflate's bound is a function of the level**, since the match search is
  limited by the chain length in the level table.

Alternatives rejected:

- Counters in loop invariants only, without instrumentation. This gives
  bounds on paper, but nothing machine-checked says the program terminates.
- A second tool with loop variants. It would not be foundational, and its
  bounds would not compose with the VST contracts.
- Waiting for native total correctness in VST. None is available.

Risks:

- **Proof overhead.** Every loop invariant gains a term relating the counter
  to progress. For zlib's loops that relation is usually linear.
- **Shared risk with goto.** If contracts cannot be carried back to the
  original code, the fallback for termination is a whole-program statement,
  which VST's top-level soundness theorem already supports.
- **Counter width.** Bounds must fit in a machine word. The checksum
  functions, which take a full-width length, need checking.

### C standard editions

Decided 2026-11-23.

We judge behavior against every edition of the C standard from 1990 through
2023. A construct is a finding if any of those editions leaves it undefined.
Reliance on implementation-defined or unspecified behavior is judged the same
way, under the policy above.

- **Findings record the editions affected.** A construct undefined under only
  one edition is still a finding, and may be ranked below one that is
  undefined under all.
- **Reference text.** We cite the 2017 edition as the primary text, since it
  is the 2011 edition with defects corrected. We keep a short table of where
  the 1990, 1999, and 2023 editions differ from it.
- **CompCert's place.** CompCert's semantics is closest to the 1999 edition.
  The table of differences between CompCert and the standard, which the
  undefined behavior policy requires, is checked against each edition.
- **Edition as a matrix dimension.** Where the edition changes the code that
  is compiled, it is a dimension of the configuration matrix. For the first
  target that affects only the files listed below.

Why:

- zlib commits to no single edition. Its documentation names none, and its
  own continuous integration builds under every edition from 1989 through
  2017 plus a draft of 2023.
- Current gcc and clang default to the 2017 or 2023 dialect, so neither the
  1989 edition zlib is written to nor the 1999 edition CompCert follows
  describes what dependents compile.
- Our policy requires correctness for any conforming compiler, and compilers
  conform to different editions.
- The editions disagree in only a few places, so the list can be audited by
  hand. Known examples are rounding in signed division with negative
  operands, left shifts of negative values, and zero-length copies involving
  null pointers.

What we measured: all fifteen library files of zlib 1.4 were preprocessed
under the 1989, 1999, 2011, 2017, and 2023 editions, and zlib's own code was
compared. Twelve files are identical under every edition, including all of
inflate, deflate, and both checksums. The check was run on an ARM Mac and
must be repeated on the real target.

| File | What changes with the edition |
|---|---|
| `zutil.c` | One bit in the value returned by `zlibCompileFlags`, under 1989 only |
| `gzlib.c` | Unbounded string formatting under 1989, bounded formatting from 1999 on |
| `gzwrite.c` | The formatted-output code is built differently under 1989, and one variadic macro call differs under 2023 |

Consequences:

- One proof covers each of the twelve identical files under every edition.
- The 1989 build of the file layer uses unbounded formatting. It is a
  distinct and weaker configuration, to be placed in a late matrix cell or
  excluded with a stated reason.

### Specification architecture

Decided 2026-11-24.

Specifications and proofs are organized in four layers with strict dependency
rules. Only the first three need to be read to know what has been proven.

| Layer | Contents | May depend on | Changes when |
|---|---|---|---|
| 1. Format | What the RFCs define: the Deflate, zlib, and gzip formats and both checksums, as mathematics over byte sequences | The Rocq standard library only | Almost never |
| 2. API behavior | What the zlib manual promises: an abstract stream state and, for each function, the allowed results, return codes, and flush behavior | Layer 1 | The manual changes |
| 3. C contracts | VST function contracts tying C memory to the abstract state, plus the cost clause | Layers 1 and 2, VST, the target's type layout | The ABI or target changes |
| 4. Proofs | Internal invariants, concrete memory layouts, transformed syntax trees, and the proofs themselves | Everything | Any source release |

Layers 1 and 2 contain no C and no VST, which keeps them reusable for other
Deflate libraries and keeps the trusted reading small. A build check enforces
the dependency rules.

Design choices:

- **We write layer 1 ourselves.** Existing formal specifications are listed
  under [Related work](#related-work). They are not our starting point. We may
  later use them as further evidence that our specification is correct.
- **Each format gets a relation and an executable decoder.** The relation says
  which bytes encode which data and is what a reviewer compares against the
  RFC. The executable version is run on test vectors and fuzzed against zlib.
  A theorem ties the two together.
- **Inflate gets two acceptance sets.** One is the set of streams the RFC
  allows. The other is the set zlib accepts, with its documented leniencies.
  A theorem states exactly how they differ.
- **Contracts are relational, not a second implementation.** The contract for
  deflate says the output is a valid stream that decodes to the input. It
  does not reproduce the match-finding algorithm. Exact functional models are
  used only where they are cheap, as with the checksums.
- **Chunking independence is proven in layer 2**, once, without touching C.
- **The stream structure is split.** Fields a caller reads and writes are
  visible in the contract. Internal state sits behind an opaque predicate.
- **Cost bounds live in layer 3.** The manual and the RFCs say nothing about
  cost, so a bound is a property of this implementation and release.

Supporting mechanisms:

- **Traceability is a data file.** Each normative sentence of the manual and
  the RFCs has an entry with its location, a hash of its text, and the theorem
  or test that covers it. CI checks that every entry resolves. On a new
  release, a changed hash flags the sentences upstream edited.
- **Claims sit on top.** The headline theorem and the verified client are
  stated using only layers 1 to 3.
- **Readability.** Each definition in the first three layers is paired with a
  prose statement and the sentence it formalizes, and rendered as a browsable
  document.
- **A size budget.** The line count of the first three layers is tracked as
  the size of what must be trusted.

What depends on the format layer:

| Claim | Depends on layer 1? |
|---|---|
| Memory safety, no undefined behavior, termination, cost bounds | No |
| Decompressing compressed data returns the original | No. It needs only internal consistency. |
| Conformance with the RFCs, and interoperability with other tools | Yes |

A reader who distrusts our format layer still gets every security guarantee.
They lose only the interoperability claim. Since we wrote that layer, its
correctness rests on its small size, its traceability to the RFCs, testing
against zlib, and external review.

Alternative rejected: a single exact functional model of zlib's behavior with
the C proven equal to it. It duplicates the algorithms in Rocq and ties the
specification to one release.

### Closing the undefined behavior gap, and secondary tools

Decided 2026-11-24.

VST leaves a known set of constructs unchecked. We close as much of that gap
as we can inside the primary proofs. Secondary tools fill what remains, and
that work is our lowest priority.

**In the primary proofs.** A small function over the Clight syntax tree lists
every left shift of a signed value, right shift of a signed value, signed
division or remainder, and conversion into a signed type that may not fit.
Each listed construct becomes an extra obligation in the VST proof, showing
the value is in range, or is discharged by its types alone. These guarantees
stay foundational and depend on no second tool.

**By hand.** Pointer casts between non-character types are audited one by one
for violations of the aliasing rules, with a ledger entry each.

**Secondary tools, lowest priority.** These are not part of Milestone 1 and
are taken up only after higher-priority work.

- **Frama-C Eva** is the chosen independent tool. It is a sound static
  analyzer for run-time errors, with its own C semantics and trusted base. It
  can also detect accesses whose result depends on evaluation order, which
  CompCert's translation erases before the proofs see the code.
- **Sanitizer fuzzing** is the dynamic tier: the pinned source built with
  clang and gcc under the undefined behavior, address, and memory sanitizers,
  for each C edition.
- **Clang's type sanitizer** may cross-check the pointer cast audit. Its
  documentation calls it experimental.

Until a secondary tool has been run, the gaps only it can close are listed as
open in the headline claim. The main one is dependence on evaluation order.

What we measured, in the syntax trees generated for the eleven core files of
zlib 1.4. The trees were generated on an ARM Mac, so the counts are
exploratory.

| Construct | Count |
|---|---|
| Left shift of a signed value | 86 of 217 left shifts |
| Right shift of a signed value | 5 |
| Signed division or remainder | 3 |
| Conversion into a signed type that may not fit | 20 |
| Pointer cast between non-character types | 24 |

Most of the signed shifts come from small unsigned types that C promotes to a
signed integer before shifting. The tree code alone has 56.

Not chosen: CBMC, which is bounded only and remains a reasonable later
addition. Cerberus and CN, which are closest to the standard's text but
describe themselves as a reference semantics for small programs and as
experimental. TrustInSoft Analyzer, which is commercial. Eva has not been run
on zlib, and its cost to reach zero alarms is unknown.

### Carrying source patches: the patch sequence

Decided 2026-11-24.

Upstream stays pristine, and every deviation from it is one file in an
ordered patch sequence.

- **Pristine upstream.** The zlib repository is a submodule pinned to the
  release commit. Nobody edits it.
- **One patch per finding.** Each patch is a single logical change in its own
  file, tied to one ledger entry. A sequence file fixes the order.
- **Generated tree.** The build applies the sequence to a copy of upstream.
  That copy is what gets preprocessed, translated, and proven. It is never
  edited by hand.
- **A short sequence is the goal.** An empty sequence would mean zlib is
  proven verbatim. The length of the sequence is a headline metric.

The full pipeline is: upstream, then the patch sequence, then preprocessing,
then CompCert's translation, then our Clight transformations, then the
proofs. Patches change what ships. Transformations do not.

What each patch carries:

- **A header** stating its class, its ledger entry, the C editions affected,
  and its upstream status. The classes are defect fix, hardening,
  provability fallback, and documentation.
- **A witness, for a defect fix.** A test that fails on unpatched upstream and
  passes with the patch. It supports the statement that zlib is correct
  except for named defects, and it becomes the regression test.

What the build checks:

- **The sequence applies cleanly**, in order, to the pinned commit.
- **"Proven as is" is derived, not asserted.** For each function, the build
  compares the syntax tree from pristine upstream with the one from the
  patched tree. Identical trees mean the theorem applies to upstream
  verbatim. Different trees mean the function is listed as proven after the
  patches that touch it.
- **The release archive matches the repository.** Distributions build from
  the release archive, not from the git tag. The build confirms the library
  sources are byte-identical in both and pins both hashes.

Points to be aware of:

- **The license requires marking.** zlib's license says altered source
  versions must be plainly marked and not misrepresented as the original. The
  generated tree is marked with a notice file. The version string is left
  alone, because changing it would alter the return value of `zlibVersion`,
  a behavior change we would then have to explain.
- **Configure edits one header.** The upstream configure script rewrites
  `zconf.h`. That step runs before translation, and its result is what gets
  checked.
- **New releases.** Intake moves the submodule to the new tag and reapplies
  the sequence. A patch that upstream has fixed drops out and is recorded as
  fixed. A patch that conflicts is refreshed.

Alternatives rejected: a fork with our commits on a branch, which shows
deviations only through a diff and needs a second repository. A modified copy
of the source checked into this repository, which hides every deviation and
makes each release a manual merge. The patch sequence can be turned into a
branch of commits mechanically when we decide to submit upstream.

## Milestones

### Milestone 1: Adler-32, end to end

Decided 2026-11-23. Not started.

Take one whole source file, `adler32.c`, through every stage of the method.
The file has five short functions, loops over a byte buffer, and no goto.

Why this first:

- It tests every decision above at small scale: the toolchain, cost
  contracts, tick instrumentation, and the "proven equals built" check.
- It answers the question behind both goto and termination, which is whether
  a contract proven for transformed code can be carried back to the original.
  That answer is needed before we invest in inflate.
- It moves one file to a final state in the status table, with a claim
  someone can check.

The trade-off is that Adler-32 is not the attack surface. This milestone
delivers a proven method more than direct security value. Everything after it
depends on the method working.

Exit criteria:

1. **Reproducible environment.** The pinned versions of Rocq, VST, and
   CompCert on the x86-64 Linux machine, with zlib 1.4 pinned by hash, rebuilt
   by one command.
2. **Proven equals built.** A mechanical check that the source given to the
   verifier matches what the upstream build compiles, for this file.
3. **Reference model.** Adler-32 as defined in RFC 1950, validated against
   test vectors and differentially against zlib.
4. **Contracts.** Every function in the file has a contract covering memory
   safety, the functional result, and a cost bound, with each precondition
   reviewed.
5. **Proofs.** VST proofs with no admitted lemmas and the assumption list
   printed.
6. **Transformation theorems.** The tick instrumentation exists as a Rocq
   function. Both generic theorems are stated, and each is either proven or
   has a recorded status.
7. **Contract transfer answered.** Either the contract is carried back to the
   original code, or we record why not and adopt the fallback. A toy function
   with a forward goto is included so the answer covers both transformations.
8. **Validation.** Mutants of the file each break a proof, and the manual's
   sentences about Adler-32 are mapped to theorems.
9. **Ledger and claim.** The findings ledger has its first entries, and the
   headline claim is written out for this one file.

Secondary tools are not part of this milestone. The listing of unchecked
arithmetic constructs and the extra VST obligations are part of it, since
they belong to the primary proofs. Dependence on evaluation order is stated
as an open gap in this milestone's claim.

Work that does not depend on the target platform can begin before the move to
the Linux machine: the reference model, the contract design, the
instrumentation function, and the toy goto experiment. The environment, the
build check, and the final proofs wait for that machine.

Progress as of 2026-11-24:

- **Criterion 3, partly done.** Layer 1 defines Adler-32 twice, from the
  prose of RFC 1950 and from its sample code, and proves the two equal.
  Test vectors pass. They were compared with the system zlib on the
  development machine, not yet with the pinned release.
- **Layer 2 written.** Specifications for `adler32`, `adler32_z`, and
  `adler32_combine`, with proofs that each can be met, that each fixes the
  result where the manual makes a promise, and that the manual's usage
  example computes the checksum of all the data however it is split.
- **Criterion 8, partly done.** All 31 sentences of the relevant passages in
  RFC 1950 and `zlib.h` are in the traceability file. Mutation testing has
  not started.
- **Criterion 9, started.** The ledger has its first entry,
  [F0001](ledger/F0001-adler32-null-buffer-length-one.md). `adler32` with a
  null buffer and a length of 1 dereferenced the null pointer, against the
  manual. It is resolved by a hardening patch with a witness test. As a
  result `adler32_z` will be listed as proven after a patch, not as is.
- **Not started:** the environment on the Linux machine, the build check,
  contracts, proofs, the transformation theorems, and contract transfer.

### Milestone 2: the inflate reference model

Planned, not yet specified in detail.

Build the executable model of inflate, including its precise acceptance set,
and fuzz zlib 1.4 against it. This has value without any C proof and may
surface real discrepancies. Its early work may overlap with Milestone 1.

## Related work

Existing work of potential interest. None of it is a starting point for our
specifications. We may later compare our format layer against some of it, by
proof or by testing, as further evidence that ours is correct.

- **An Implementation of Deflate in Coq.** Christoph-Simon Senjak and Martin
  Hofmann, LMU Munich. Peer reviewed in 2016 and the basis of Senjak's 2018
  doctoral thesis. A relational specification of the Deflate bit format with
  a verified compressor and decompressor.
  [Paper](https://arxiv.org/abs/1609.01220),
  [thesis](https://www.cse.chalmers.se/~abela/PhD-Christoph-Senjak-2018.pdf),
  [code](https://github.com/dasuxullebt/DampFnudeL). It covers raw Deflate
  only, was last updated in 2017, and has no license for the project itself.
- **lean-zip.** A Deflate, zlib, and gzip implementation in Lean 4 with a
  machine-checked round-trip theorem and specifications for both checksums.
  [Repository](https://github.com/kim-em/lean-zip), Apache-2.0. Its README
  states that the code and proofs were written by loosely supervised AI
  agents. An independent fuzzing study is described in
  [this write-up](https://kirancodes.me/posts/log-who-watches-the-watchers.html).
- **`puff.c`.** A simple decoder by Mark Adler, shipped in zlib's `contrib`
  directory. Its header says it was written to specify the Deflate format
  unambiguously. It is not formal, but it is the most authoritative
  executable statement of the format.
- **RFCs 1950, 1951, and 1952.** The prose definitions of the zlib, Deflate,
  and gzip formats.

A survey of 2026-11-23 found no formal specification of CRC-32 or Adler-32
from an established group, and no Deflate formalization in Isabelle, HOL4, or
F*.

## Open decisions

Listed roughly in order of consequence.

1. **Repository layout and CI.** A provisional layout is in use, described
   under [What is in the repository](#what-is-in-the-repository).

## Planned spikes

Small experiments that inform decisions above. None has been run.

- **Contract transfer.** On a toy function with a forward goto, show that a
  behavior-preservation theorem for the Clight transformation can carry a VST
  contract from the transformed function back to the original. Part of
  Milestone 1.
- **Backward jumps.** Find a transformation for the two loops in the fast
  inflate path.
- **Termination.** Instrument Adler-32 with the tick counter, prove its cost
  contract in VST, and state the two generic theorems precisely enough to
  judge their difficulty. Part of Milestone 1.
