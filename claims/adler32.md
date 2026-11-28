# The claim for `adler32.c`

Written 2026-11-26, for Milestone 1. Revised 2026-11-27: the step from the
contracts to executions is now a theorem for whole programs, and the one
obligation the claim relied on, T0003, is proven. The three sentences of
the claim are unchanged. What they rest on is stated more exactly.

This is a claim about one source file of zlib, the smallest of fifteen. It
is not a claim about zlib. Nothing here says that inflate or deflate is
correct or safe.

## The claim

> For zlib 1.4 with one hardening patch, in the upstream default
> configuration for x86-64 Linux, it is machine-checked that every call to a
> function of `adler32.c` that meets the function's stated precondition is
> memory safe, changes none of the caller's memory, and returns the value
> the zlib manual promises, as RFC 1950 defines it. This holds for the C
> source under CompCert's semantics of C. It does not yet extend to
> termination, to everything ISO C leaves open, or to the compiled library.

The rest of this file makes each part exact: what the words stand for, what
the claim rests on, and what it leaves out. The limits take as much room as
the result, on purpose.

`claims/adler32.toml` lists what the claim refers to in the repository, and
`tools/check_claim.py` checks that list in every full build.

## What the words stand for

### zlib 1.4 with one hardening patch

- **The release.** zlib 1.4, tag `v1.4`, commit
  `99623ef7097352da7993ba614161fd6a311e046e`. It is a git submodule pinned
  to that commit.
- **The patch.**
  `patches/0001-adler32-null-buffer-before-one-byte-path.patch`. It is the
  whole patch sequence.
- **Why there is a patch.** The manual says that `adler32` returns the
  initial value when the buffer is null, and puts no condition on the
  length. In zlib 1.4 as released, a null buffer with a length of 1 reads
  through the null pointer. That is finding
  [F0001](../ledger/F0001-adler32-null-buffer-length-one.md). The patch
  moves the test for a null buffer in front of the one-byte path.
- **The claim is false for unpatched zlib 1.4**, for that one call. The
  proof of the null-buffer case fails against the unpatched file, and a
  test program that makes the call is killed on the unpatched build and
  passes on the patched one.
- **The patch has not been offered upstream.**

### The upstream default configuration for x86-64 Linux

- **How the source is configured.** As the upstream `./configure` sets it
  up with no options, on x86-64 Linux, where `long` and pointers have 64
  bits. The verifier is given the file with the flags
  `-DHAVE_UNISTD_H -DHAVE_STDARG_H -DHAVE_HIDDEN -D_LARGEFILE64_SOURCE=1`.
- **Proven equals built.** `tools/check_build.py` runs the real
  `./configure` and `make`, and compares what gcc is given with what the
  verifier is given, token by token after preprocessing. For `adler32.c`
  they agree over 2655 tokens, for the static and the shared library, apart
  from one accepted difference: an attribute that hides two symbols from
  other libraries at link time.
- **Code this configuration does not compile is not covered.** The file
  has a second set of macros for processors without a divide instruction,
  under `NO_DIVIDE`. They are not built here and nothing is proven about
  them.

### Every function of `adler32.c`

| Function | State | Contract |
|---|---|---|
| `adler32_z` | Proven after patch 0001 | `adler32_z_contract` |
| `adler32` | Proven as is | `adler32_contract` |
| `adler32_combine_`, internal | Proven as is | `combine_internal_spec` |
| `adler32_combine` | Proven as is | `adler32_combine_funspec` |
| `adler32_combine64` | Proven as is | `adler32_combine64_funspec` |

`adler32` is unchanged by the patch, but it calls `adler32_z`, so what is
proven of it holds only with the patched `adler32_z`.

One Rocq theorem covers the file: `adler32_c_verified`, in
`proofs/adler32/WholeFile.v`. It says that every function defined in the
file, as CompCert translates it, has a contract in one list, and that its
body meets that contract when the functions it calls meet theirs from the
same list. It speaks of every function in the translated file, so a
function added without a proof would make it fail.

### That meets the function's stated precondition

Every clause of every precondition is reviewed in
[audit/preconditions-adler32.toml](../audit/preconditions-adler32.toml).
What a caller must ensure comes to this.

- **`adler32_combine` and `adler32_combine64`: nothing.** Any three
  argument values may be passed.
- **`adler32_z` and `adler32` with a null buffer: nothing.** Any checksum
  argument and any length may be passed.
- **`adler32_z` and `adler32` with a buffer:**
  1. The `len` bytes at the pointer lie in an array the caller holds.
  2. That array is live, and has at least one cell.
  3. If `len` is not zero, the caller may read those bytes, and nothing
     else writes them during the call.
  4. The caller lends the array for the length of the call.
  5. Those bytes are initialized. They may have any values.

No precondition constrains the content of the data or the value of the
checksum argument.

### Is memory safe, and changes none of the caller's memory

A proven contract is a statement in VST's logic. What it means for a
running program comes from VST's soundness theorem: a program in which
every function meets its contract does not get stuck in CompCert's
semantics. So it does none of these: read or write outside an object, use
a null or dangling pointer, read uninitialized memory, overflow a signed
integer, divide by zero, or shift by too much.

That step is now a theorem of ours, for whole programs:

- **For any program.** `verified_program_never_goes_wrong`, in
  `proofs/lib/Soundness.v`. A program that VST has verified, and whose
  `main` has a simple shape, never goes wrong in CompCert's semantics of
  Clight. It applies VST's soundness theorem and adds what that theorem
  does not give: see "What the claim rests on", item 4.
- **For one program that calls all five functions.**
  `client_never_goes_wrong`, in `proofs/adler32_client/Client.v`. The
  program is `proofs/adler32_client/client.c`. Its `main` makes seven
  calls: a null buffer, a whole buffer, the same buffer in two pieces, and
  the two checksums combined. The five functions in it are checked to be
  the very syntax trees the contracts are proven for.

What this does and does not give:

- **It is about a whole program.** There is no such theorem for a
  function alone, since a function does not run alone. "Every call that
  meets the precondition" becomes: every call made by a program whose
  other functions are verified too. For such a program the general
  theorem applies. We have applied it to one.
- **It holds under two hypotheses about external calls.** They are in the
  statement of each theorem: `more_permission_same_call`, which VST's own
  theorem takes, and `inline_calls_deterministic`, which we add. Neither
  is proven. The client program makes no external call.
- **It says the program does not get stuck.** The values the functions
  return are in the contracts, and do not appear in the statement about
  executions.

The contract's postcondition returns the caller's array exactly as it was
lent, under the same share. The combine functions touch no memory at all.

### Returns the value the zlib manual promises, as RFC 1950 defines it

The promises are in `spec/api/Adler32.v`, written from the manual, in terms
of the definition of Adler-32 in `spec/format/Adler32.v`, written from
RFC 1950.

- **`adler32` and `adler32_z`, null buffer.** The result is 1, the initial
  value.
- **`adler32` and `adler32_z`, with a buffer.** If the checksum argument
  is the Adler-32 checksum of some earlier bytes, the result is the
  Adler-32 checksum of those bytes followed by the buffer. For every
  checksum argument, the result is below 2^32.
- **`adler32_combine` and `adler32_combine64`.** If the first two
  arguments are the checksums of two sequences of bytes, and the third is
  the length of the second sequence, the result is the checksum of the two
  sequences joined.

Where the manual promises nothing, the claim promises no value:

- **A checksum argument that is not a checksum.** `adler32` and
  `adler32_z` are still memory safe and still return a value below 2^32.
  The combine functions may return a value that does not fit in 32 bits.
- **A negative length given to a combine function.** The manual says the
  result "has no meaning or utility".

A caller can tell from a value alone whether it is a checksum: it must fit
in 32 bits, and both of its halves must be below 65521. That is
`checksum_form_iff` in `spec/api/Adler32Facts.v`.

## What the claim rests on

Everything below is trusted, not proven.

1. **The Rocq kernel**, version 9.2.0, which checks every proof.
2. **Six axioms.** No proof depends on any other, and no lemma is
   admitted. The build checks that for every result named here. All six
   are assumed by VST and CompCert, not added by this project.
   - `Classical_Prop.classic`: excluded middle.
   - `FunctionalExtensionality.functional_extensionality_dep`: functions
     that agree everywhere are equal.
   - `Axioms.prop_ext`: propositions that imply each other are equal.
   - `Ensembles.Extensionality_Ensembles`: sets with the same members are
     equal.
   - `ClassicalDedekindReals.sig_not_dec` and
     `ClassicalDedekindReals.sig_forall_dec`: two axioms behind the
     standard library's real numbers.

   The specifications themselves, in `spec/`, depend on no axiom.

   **Five more for the statements about executions.** The theorems named
   under "Is memory safe" and the result about the remainder in limit 2
   depend on these as well. They come with VST's soundness theorem and
   with CompCert's semantics. The build checks them against
   `audit/execution-axioms.txt`. The proofs of the contracts do not depend
   on them.
   - `lib.Axioms.proof_irr`: two proofs of one proposition are equal.
     CompCert's.
   - `Eqdep.Eq_rect_eq.eq_rect_eq`: the same for equality proofs. The
     standard library's.
   - `Clight_core.inline_external_call_mem_events`: an external call that
     may be expanded inline changes memory in a way a list of memory
     operations describes. VST's.
   - `Events.external_functions_properties` and
     `Events.inline_assembly_properties`: what CompCert assumes of
     external functions and of inline assembly.
3. **CompCert 3.18 as the meaning of C.** The proofs are about the Clight
   program that CompCert's front end makes from the source file. That the
   front end reads C correctly, and that CompCert's semantics is a right
   reading of the C standard, are both trusted.
4. **VST 2.17.** The contracts are statements in VST's program logic.
   What such a statement means for executions is given by VST's own
   soundness theorem, which is proven in Rocq against CompCert's
   semantics. We have now applied that theorem, in
   `proofs/lib/Soundness.v`. It did not give "never goes wrong" as it
   stands, and four things had to be added. Each is a way the result is
   narrower than the words "VST is sound" suggest.
   - **A hypothesis VST's theorem takes and does not prove,**
     `more_permission_same_call`: an inline external call behaves the same
     on a memory that grants more permissions.
   - **A hypothesis of ours,** `inline_calls_deterministic`. VST's theorem
     says that some execution is safe. CompCert asks it of every
     execution. The two agree where each step has one outcome, and the
     external calls VST executes as steps are where that is not known.
   - **That `main` returns an integer.** CompCert counts a program as
     finished when `main` returns an integer, VST when it returns
     anything. We prove the difference away for a `main` with no loop, no
     jump, and a `return` of a value on every path. It also uses that
     pointers have 64 bits.
   - **That VST's copy of the step relation agrees with CompCert's.**
     Proven.
5. **The specification text.** Four files have to be read and believed:
   `spec/format/Bytes.v`, `spec/format/Adler32.v`, `spec/api/Adler32.v`,
   and the contracts in `proofs/adler32/Contract.v` and the head of
   `proofs/adler32/Combine.v`. They hold definitions only, about 350 lines
   with their comments. If they say something other than what RFC 1950 and
   the manual say, the proofs prove the wrong thing.
6. **The build check**, and the one difference it accepts.
7. **The pinned environment.** A container, defined by one file, with
   every package version fixed. The system headers the file is
   preprocessed with are the container's.

## Unproven obligations

The ledger holds three obligations about program transformations. One is
now proven, and two are stated and not proven. The claim stands to them
as follows.

- **[T0003](../ledger/T0003-arithmetic-guards.md), relied on, and proven
  on 2026-11-27.** If a program with guards never goes wrong, then in the
  program without them no guard's condition ever holds. It is
  `guards_removed` in `proofs/lib/GuardSound.v`. So the claim no longer
  rests on an unproven obligation of ours. See the second limit below for
  what the theorem gives here.
- **[T0002](../ledger/T0002-tick-instrumentation.md), not relied on.** It
  is about cost, and the claim says nothing about cost.
- **[T0001](../ledger/T0001-goto-elimination.md), not relied on.** It is
  about goto, and `adler32.c` has none.

## Evidence beside the proofs

None of this is proof. It bears on whether the specifications are right and
whether the proofs mean what they seem to.

- **Traceability.** The 31 sentences about Adler-32 in RFC 1950 and
  `zlib.h` are each mapped: 13 to a definition, 7 to a theorem, 1 to a
  test, 9 marked not covered with a reason, and 1 pending. The pending one
  belongs to the stream format of a later milestone. Two of the 31 are
  mapped to items in the C proofs, so they are covered for this
  configuration only, and each entry says so.
- **Two readings of the RFC agree.** Adler-32 is defined once from the
  prose of RFC 1950 and once from its sample code, and the two are proven
  equal.
- **A differential test.** zlib as gcc builds it returns what the model
  says on 5098 cases, in three builds: unpatched, patched, and patched
  with gcc's address and undefined-behavior checkers. This is the only
  evidence here about compiled code.
- **Mutation testing.** Of 525 small changes to the file, 521 make a proof
  fail. The other 4 are explained: 2 are the same program, and 2 change a
  value the manual gives no meaning.
- **A review of every precondition**, which removed two demands that
  nothing needed.
- **Continuous integration** rebuilds the container from nothing on a
  hosted machine and reruns every check and proof.

## What is not claimed

1. **Termination and cost.** The claim says nothing about whether a call
   returns, or how long it takes. What exists:
   - Cost bounds are proven for copies of the five functions with a
     counter added, for every call the claim covers: 1 tick for
     `adler32_z` with a null buffer, `len/5552 + len/16 + 19` with a
     buffer of `len` bytes, one more for `adler32`, and 2 for the combine
     functions. The same proofs show that these copies return what the
     functions as shipped are proven to return. One theorem states it for
     the file: `adler32_c_verified_with_ticks`.
   - That few ticks mean few steps is proven.
   - That removing the counter leaves the behavior unchanged is stated and
     not proven. See [T0002](../ledger/T0002-tick-instrumentation.md).
   - The contracts with a cost bound are not joined to VST's soundness
     theorem. Only the ones without are, and for one program.

   So there is no theorem that any call to these functions terminates.
2. **Everything ISO C leaves open.** The proofs hold under CompCert's
   semantics. A compiler may differ from it wherever the C standard
   leaves behavior undefined, implementation-defined, or unspecified and
   CompCert picks one meaning.
   - **Listed and dealt with:** signed shifts, signed division and
     remainder, and conversions into a signed type that may not fit. The
     file has two such places. `NMAX / 16` is closed by its constants.
     `len2 %= BASE` is shown never to see a negative operand, by a proof
     about a copy of the function with a test added in front of it. That
     the result carries over to the function without the test is
     [T0003](../ledger/T0003-arithmetic-guards.md), now proven. Like every
     statement about executions it is about a whole program. For the
     client program it is `remainder_operand_not_negative`, in
     `proofs/adler32_client/Guarded.v`: whenever that program is about to
     run the statement, `len2` is not negative.
   - **Open:** dependence on the order in which operands are evaluated.
     CompCert fixes an order before the proofs see the code. Closing this
     needs a second tool, which has not been run.
   - **Not examined:** the aliasing rules, and pointer arithmetic that
     leaves an object.
3. **The compiled library.** Nothing is proven about the machine code gcc
   or any other compiler produces. The proofs are about the source. The
   differential test is the only evidence about the binary.
4. **Other configurations.** One cell of the configuration matrix. Not
   32-bit targets, not Windows, not big-endian machines, not the
   `NO_DIVIDE` code.
5. **Two calls with a length of zero that C allows on this target.** A
   pointer to an allocation of size zero, and a pointer that is not null
   and points to no object. The tools cannot describe either. A caller
   holding such a pointer can skip the call.
6. **The callers inside zlib.** inflate and deflate call `adler32`.
   Nothing is proven about them, including that they meet its
   precondition.
7. **Use from several threads.** The contracts say what one call needs to
   own. Nothing more is claimed about concurrent use.
8. **Stack use.** The semantics the proofs rest on has no bound on the
   stack. None of the five functions is recursive.
9. **How good a checksum Adler-32 is.** Nothing is claimed about which
   errors it detects.
10. **Review by anyone else.** The specifications have not been read by a
    zlib expert or a verification expert, and no second tool has checked
    the same source.

## How to check it

With Podman and the repository cloned with its submodule:

```
tools/in-container.sh make full
```

That builds the container, applies the patch, runs the build check and the
differential test, checks every proof, prints what each proof depends on,
and checks the references in this file. It takes about ten minutes after
the container is built. Mutation testing is separate, and takes much
longer:

```
tools/in-container.sh make mutants
```
