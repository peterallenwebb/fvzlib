# Proofs of the Adler-32 C contracts

Layers 3 and 4 for `adler32.c` of patched zlib 1.4: the C contracts and the
VST proofs that the code meets them.

Checked on 2026-11-26 on the project's first target, x86-64 Linux, in the
toolchain container, with Rocq 9.2.0, CompCert 3.18, and VST 2.17. They were
first checked on 2026-11-24 on an ARM Mac and carried over to the target the
next day with no change to any proof script. `make full` at the top of the
repository runs them. `make check` does not, because they need VST.

## What is proven

The functions proven are the real ones from the patched tree, with no
instrumentation and no transformation. `adler32.c` contains no goto, so the
contracts attach directly to the code that ships.

Each function has one contract. It covers every call the manual allows,
apart from two kinds of call with a length of zero that the tools cannot
describe. See "The buffer of length zero".

| Function | Contract | Proven |
|---|---|---|
| `adler32_z` | `adler32_z_contract`, in `Contract.v` | Memory safe, the caller's memory unchanged, result below 2^32, and result satisfies the Layer 2 specification. For a null buffer of any length, or a run of bytes of any length, including zero, inside a non-empty array the caller owns. The rest of the array may hold anything. Any 64-bit checksum argument. |
| `adler32` | `adler32_contract`, in `Contract.v` | The same, with a 32-bit length |
| `adler32_combine` | `adler32_combine_funspec`, in `Combine.v` | Result satisfies the Layer 2 specification, for any two 64-bit arguments and any 64-bit signed length |
| `adler32_combine64` | `adler32_combine64_funspec`, in `Combine.v` | The same |

The contracts of `adler32_z` and `adler32` are derived from three narrower
contracts for each, which are what the proofs about the C code establish:

| Function | Case | Proven |
|---|---|---|
| `adler32_z` | Null buffer, any length | Returns a value satisfying the Layer 2 specification, which is the initial value 1 |
| `adler32_z` | Non-null, non-empty buffer, any 64-bit checksum argument | Memory safe, buffer unchanged, result below 2^32, and result satisfies the Layer 2 specification |
| `adler32_z` | Non-null buffer of length zero, any 64-bit checksum argument | Memory safe, nothing read, the caller's array unchanged, result below 2^32, and result satisfies the Layer 2 specification |
| `adler32` | Null buffer, any length | As for `adler32_z` |
| `adler32` | Non-null, non-empty buffer | As for `adler32_z` |
| `adler32` | Non-null buffer of length zero | As for `adler32_z` |
| `adler32_combine` | Any two 64-bit arguments and any 64-bit signed length | Result satisfies the Layer 2 specification |
| `adler32_combine64` | The same | The same |

Every function in `adler32.c` is covered: the four exported functions above
and the internal function that both combine functions call. One theorem
says so for the file as a whole: `adler32_c_verified`, in `WholeFile.v`.
The claim built on it, with its limits, is in
[claims/adler32.md](../../claims/adler32.md).

"Satisfies the Layer 2 specification" means, for `adler32_z` and `adler32`:
if the checksum argument is the Adler-32 checksum of some earlier bytes, the
result is the Adler-32 checksum of those bytes followed by the buffer, as RFC
1950 defines it. For the combine functions it means: if the two arguments
are the checksums of two byte sequences and the length is that of the
second, the result is the checksum of the two sequences joined.

Every proof rests on VST's standard axioms only. The build checks that:
`AxiomAudit.v` prints what each result depends on, and
`tools/check_axioms.py` requires every axiom printed to be one of the six in
`audit/allowed-axioms.txt`.

## Cost: the form with ticks

Each contract also exists in a form with ticks, in `CostContract.v`. It is
a contract for the function with a counter added. It says everything the
plain contract says, and also that the call spends at most a stated number
of ticks. One tick is spent on entry to a function and one at each test of
a loop condition, including the last test, which fails.

| Function | Bound in ticks |
|---|---|
| `adler32_z`, null buffer | 1 |
| `adler32_z`, a buffer of `len` bytes | `len/5552 + len/16 + 19` |
| `adler32` | One more than `adler32_z` |
| Internal combine function | 1 |
| `adler32_combine`, `adler32_combine64` | 2 |

What is proven, checked on 2026-11-26:

- **The functions with ticks meet these contracts**, for every call the
  plain contracts cover: a null buffer, a buffer of length zero, and a run
  of bytes inside a larger array. Each proof establishes memory safety, the
  value returned, and the cost bound together. The functions are computed
  from the translated source by the instrumentation in `proofs/lib/Ticks.v`,
  and removing the ticks gives back each original body exactly.
- **The two forms come from one definition.** `with_ticks`, in
  `proofs/lib/TickLogic.v`, makes the form with ticks from the precondition
  and postcondition of a plain contract. It adds a counter that holds at
  least the cost before the call, and holds what was not spent after it.
  For each function, a lemma named `..._two_forms` states that the plain
  contract and the generated one are made of the same precondition and
  postcondition.
- **Each form is also written out by hand**, so that it can be read and
  used in the proof of a caller. Each written contract and its generated
  one are proven to follow from each other.
- **One theorem covers the file**: `adler32_c_verified_with_ticks`, in
  `WholeFile.v`. For every function the translated file defines, the
  instrumented function meets its contract with a cost bound.

The limits:

- **These are contracts for instrumented code.** That the functions as
  shipped take a bounded number of steps does not follow yet. It needs the
  second theorem of ledger entry T0002, which is stated and not proven,
  and it needs these contracts to be joined to VST's soundness theorem.
  There is still no theorem that any call terminates.
- **The bound is an upper bound.** A buffer of length zero spends 2 ticks,
  and its bound is 19, the value of the formula at zero. A buffer of one
  byte spends 1.
- **The proofs repeat the plain ones.** The proof for `adler32_z` with
  ticks follows `Verif.v` step by step, with one more clause in each loop
  invariant and one more step for each tick. We do not yet have a way to
  run one proof script against both forms. A change to the function has
  to be made in both.
- **Checking both directions mattered.** A first version of `with_ticks`
  dropped the arguments of the call. Its generated contracts could never
  be met, so every written contract implied them trivially. The converse
  lemma failed and showed the error.

## One contract per function

`Contract.v` holds the contract a caller should use. It describes the buffer
argument as either null, or a run of bytes inside an array the caller owns,
with what the array holds before and after the run named. The run may be
empty. The array may not be. Only the run has to hold bytes. The cells around
it may hold anything and may be uninitialized, since the function does not
read them.

`ContractProof.v` does not prove that contract against the C code a second
time. For any one call, the contract follows from one of the three narrower
contracts, and which one depends on the buffer argument. VST's rule for
replacing a contract by one it implies gives the result for that call. A
small lemma, `semax_body_pointwise`, collects the calls into one contract.

Three things to know about it:

- **It covers a call that none of the three covers directly**: a non-empty
  run of bytes inside a larger array. That follows from the contract for a
  non-empty buffer, because the rest of the array is not touched. The rest
  need not be initialized.
- **Nothing was lost.** Each of the six narrower contracts is proven to
  follow from the single contract of its function.
- **The three proofs about `adler32_z` are now stated with no assumptions
  about other functions.** The function calls none, and the derivation needs
  the three to share one context.

## The buffer of length zero

The manual allows a call with a buffer that is not null and a length of
zero. The code reads nothing in that call, but it does compare the pointer
with null. C defines that comparison only for null and for a pointer into an
object or one past its end. So the contract cannot accept any value at all
as the pointer.

Following the Layer 3 design, the contract asks for a position in a
non-empty array that the caller owns. The position may be anywhere from the
first byte to one past the last. The proof shows that the comparison is one
C defines, that the loop over the bytes exits before it reads, and that the
array comes back unchanged.

Since nothing is read, the contract asks nothing about what the array holds,
and does not ask for the right to read it. Until the review of 2026-11-26 it
asked for both. That excluded a call that real code makes: a loop reads into
a buffer that has never been written, the first read finds no data, and the
loop passes the buffer with a length of zero. That call is now covered, and
`fresh_array_accepted` in `ContractReview.v` states it.

For no bytes, the Layer 2 specification says a genuine running checksum
comes back as it went in. The code returns the two halves of its argument,
each reduced modulo 65521, which is the same value for every genuine
checksum.

Two calls with a length of zero are outside this contract, though C allows
them on this target. Both are limits of the tools, and neither is covered by
any claim made here.

- **A pointer to an allocation of size zero**, such as some implementations
  return from `malloc(0)`. CompCert's memory model has no position in such a
  block that it accepts in a comparison, so VST cannot prove anything about
  that call.
- **A pointer that is not null and points to no object**, such as the aligned
  constant Rust uses for an empty vector. VST accepts as a pointer argument
  only null or an address inside a block.

A caller who may hold such a pointer can skip the call when the length is
zero. For a genuine checksum the call returns its argument.

## Review of preconditions

Every clause of the precondition of every contract is listed in
[audit/preconditions-adler32.toml](../../audit/preconditions-adler32.toml)
with a verdict and a reason. Three questions were asked of each: is it
needed, can the caller meet it and know that it has, and does it constrain
the content of the data. `tools/check_preconditions.py` reads the contracts
from their source and fails if a clause is not in the review, or if a
definition the review quotes has changed. `make check` runs it. So a
precondition cannot be added or changed without the review changing too.
The tool does not judge the reasons.

The review of 2026-11-26, in numbers. A clause is one item of a
precondition, or one part of a definition it uses.

| Verdict | Clauses | Meaning |
|---|---|---|
| type | 13 | Only gives an argument its C type. Every value of the type meets it. |
| names | 14 | Only says which value is passed as which argument. |
| nothing | 8 | Asks nothing of the caller. |
| defined | 6 | Refers to a definition that is reviewed under its own name. |
| needed | 5 | The code cannot do without it. |
| promise | 4 | A condition on the promised result. The call is safe without it. |
| limit | 2 | Stricter than C requires, because of a limit of the tools. |
| ticks | 3 | About the counter that only a function with ticks has. |

The forms with ticks are not reviewed clause by clause. Each is tied to its
plain contract by the three lemmas described under "Cost: the form with
ticks", and the tool checks that those lemmas exist. What `with_ticks` adds
to a precondition is reviewed once: the counter holds at least the cost,
and the caller owns it. Those are the three clauses marked "ticks". They
ask nothing of a caller of the function as shipped, which has no counter.

What the caller of `adler32_z` or `adler32` must ensure comes to this, the
five clauses that are needed:

1. **The `len` bytes at the pointer lie in an array the caller holds.** No
   function could return the checksum without reading all of them: changing
   any one byte changes the checksum. That is `adler32_one_byte_changed` in
   Layer 1.
2. **That array is live**, so that the pointer may be compared with null.
3. **If `len` is not zero, the caller may read those bytes**, which also
   means no other thread writes them during the call. The manual does not
   say this. It is the usual rule for a C function that reads a buffer, and
   we propose no change to the manual.
4. **The caller lends the array for the length of the call.** It comes back
   unchanged.
5. **Those bytes are initialized.** They may have any values. C itself is
   laxer here: read as `unsigned char`, uninitialized memory gives an
   unspecified value. This project claims that no uninitialized memory is
   read, so a caller who checksums such memory is outside the contract.

For a null buffer nothing is asked. The combine functions have no
precondition at all beyond the types of their arguments: any three values
may be passed.

The four conditions on the promise are in the Layer 2 specifications. The
result of `adler32_z` is the updated checksum only if the checksum argument
is the checksum of some earlier data. The result of a combine function is
the combined checksum only if both arguments are checksums and the length is
that of the second sequence. Without them the contracts still hold, and
promise less:

- `adler32(0xFFFFFFF0, buf, 1)` with a zero byte returns `0xFFFEFFF0` on
  this target. That is below 2^32, as the contract says, and its upper half
  is not below 65521.
- `adler32_combine(0xFFFFFFF0, 0xFFFF0000, 1)` returns `0x1000BFFEF`, which
  does not fit in 32 bits.

A caller can test a value it did not compute. `checksum_form_iff` in
Layer 2 proves that a value is the checksum of some data exactly when it
fits in 32 bits and both of its halves are below 65521.

No clause constrains the content of the data.

What the review changed:

- **The array around the run may hold anything.** It had to hold
  initialized bytes. Nothing needed that. See "The buffer of length zero"
  above for the call it excluded.
- **An empty run needs no right to read.** It needed one. The difference
  matters only to a caller that holds a part of the ownership of an array
  that does not allow reading.
- **A second limit of the tools is recorded**: the pointer that is not null
  and points to no object.

The limits of the review:

- **The reasons are prose.** Ten Rocq results back parts of them, and the
  tool checks that those results exist. That a clause is needed is argued,
  not proven, except for the first of the five above.
- **The two values above were observed by running zlib**, on 2026-11-26,
  pristine and patched. No part of the build repeats that.
- **Conditions that are not clauses are not in the review.** A VST contract
  says nothing about how deep the stack may grow. And every contract here
  is for this target, where `unsigned long` has 64 bits.
- **The cost functions are not reviewed as preconditions.** The review
  covers what `with_ticks` asks. Whether each bound is the right one is a
  matter for the postcondition and the proof.

## What is not proven here

- **Two zero-length calls that C allows.** A pointer to an allocation of
  size zero, and a pointer that is not null and points to no object. See
  "The buffer of length zero".
- **A 32-bit range for the combine functions.** Their contract does not
  promise that the result fits in 32 bits. For arguments that are not
  checksums it need not, and the manual promises nothing for those.
- **Termination of the code as shipped.** The cost bounds are proven for
  the functions with ticks. See "Cost: the form with ticks" for what is
  still needed to carry them to the functions without.
- **A theorem about executions, in this directory.** `WholeFile.v` puts
  the five proofs into one statement, `adler32_c_verified`: every function
  the file defines meets its contract when the functions it calls meet
  theirs. That is the premise of VST's rule for linking, not its
  conclusion. A library does not run by itself, so the step to executions
  is taken for a whole program that calls these functions, in
  [proofs/adler32_client](../adler32_client/README.md). It is one program,
  and the step is taken for the contracts without a cost bound only.
- **The rest of the gap VST leaves.** The arithmetic VST does not check is
  listed and dealt with below. Aliasing, pointer arithmetic that leaves an
  object, and evaluation order are not addressed.

## Arithmetic that VST does not check

`CensusAdler32.v` lists, for every function in the file, each signed shift,
signed division or remainder, and conversion into a signed type that may
not fit. See [proofs/lib](../lib/README.md) for what the census is. The
whole list for `adler32.c` has two items.

| Function | Item | Status |
|---|---|---|
| `adler32_z` | `NMAX / 16`, a signed division | Closed by its constants, 5552 and 16 |
| Internal combine function | `len2 %= BASE`, a signed remainder | Open, then closed by proof |

The remainder is implementation-defined in the 1990 C standard when `len2`
is negative. `CombineGuarded.v` applies the guard transformation, which puts
a test for a negative `len2` in front of that statement, and proves the same
contract for the guarded function. VST can only prove the guard's jump
unreachable, so the proof shows `len2` is never negative there.

Two honest limits. The guarded proof repeats the steps of the plain proof,
since we do not yet have a way to run one proof script against both forms of
a function. And the step from "the guarded function never gets stuck" to
"the original never takes a remainder of a negative value" is a statement
about a whole program running, not about the function alone. It was the
obligation T0003 in the ledger, and was proven on 2026-11-27. For the
client program in [proofs/adler32_client](../adler32_client/README.md) the
conclusion is a theorem: whenever that program is about to run
`len2 %= BASE`, `len2` is not negative.

## The patch matters

The null-buffer proof goes through only for the patched source. Against
pristine zlib 1.4 it fails at the one-byte path, where VST asks for memory
at the null pointer. That is finding F0001, seen from the proof's side.

## Mutation testing

A contract that says too little is met by too many programs. To test for
that, `tools/check_mutants.py` changes `adler32.c` in one small way, checks
the proofs in this directory against the changed file, and repeats that for
every change it knows how to make. A changed file is a mutant. A mutant is
killed when a proof file fails, and survives when every proof still checks.

The runs of 2026-11-25, on the patched file:

| | Mutants |
|---|---|
| Made | 624 |
| Dropped: `clightgen` rejects the file | 33 |
| Dropped: the change is in code this configuration does not compile | 66 |
| Checked against the proofs | 525 |
| Killed | 521 |
| Survived | 4 |

The 66 are in the macros for processors without division, under
`NO_DIVIDE`. The 33 are uses of one variable for another whose type does
not fit.

| Kind of change | Killed | Survived |
|---|---|---|
| One operator replaced by a near one, such as `<` by `<=` | 81 | 0 |
| One integer constant raised or lowered by one | 63 | 2 |
| One assignment or macro call removed | 44 | 0 |
| The condition of one `if` or `while` negated | 17 | 0 |
| One use of a variable replaced by another variable of the function | 308 | 2 |
| One returned expression raised by one | 7 | 0 |
| The file as upstream released it, without our patch | 1 | 0 |

| Proof that fails first | Mutants |
|---|---|
| `body_adler32_z_buffer` | 287 |
| `body_adler32_z_null` | 15 |
| `body_adler32_buffer` | 7 |
| `body_combine_internal` | 198 |
| `body_adler32_combine` | 7 |
| `body_adler32_combine64` | 7 |

Every function of the file has mutants, and every one of them is killed
apart from the four below.

The four survivors, all in the internal combine function. Each is listed
with its reason in
[audit/mutants-adler32.toml](../../audit/mutants-adler32.toml), and the
tool fails if a mutant survives that is not listed there.

1. **Two are the same program.** After `rem = (unsigned)len2`, the two
   variables hold the same number, at least 0 and below 65521. Using `len2`
   for `rem` in `rem * sum1`, or in `BASE - rem`, changes a type and not a
   value, since C converts either one to `unsigned long` there. The mutant
   returns what the original returns for every argument.
2. **Two change the value returned for a negative length.** The code
   returns `0xffffffff`, which its comment calls a clue for debugging. The
   manual says the result then "has no meaning or utility", the Layer 2
   specification allows any result, and so the contract does not fix that
   constant. One of the two mutants returns 4294967296, which does not fit
   in 32 bits. The contract allows that too. If we later decide a caller
   may rely on the debugging value, the place to say so is Layer 2.

So no survivor shows a contract that promises less than the manual does.

The limits:

- **Killed does not mean wrong.** A kill means the proof script no longer
  checks. Changing `while (len >= 16)` to `while (len > 16)` sends a last
  block of exactly 16 bytes through the loop that takes one byte at a time
  and not through the unrolled one. The sums are the same, and the mutant
  is killed, because the proof is written for the code as it stands. We
  have not counted how many of the 521 are such programs. What
  the kills show is that the proofs follow this code token by token. What
  bears on the strength of the contracts is the survivors, and there the
  result is as above.
- **The changes are small and single.** One token or one statement at a
  time. Not tried: two changes together, an added statement, a removed
  `return`, a changed type or cast, or a change inside a macro body other
  than swapping `adler` and `sum2`.
- **Only this configuration.** The `NO_DIVIDE` code is not compiled, so its
  66 mutants were not tested.
- **The proofs with ticks killed nothing.** A mutant is killed by the
  first file that fails, and for all 521 that is a plain proof. Only the 4
  survivors reached the proofs with ticks, and they pass them, as they
  must. So the runs do not show what the proofs with ticks would catch on
  their own.
- **No historical vulnerability to reintroduce.** The project plans to
  reintroduce each fixed vulnerability as a mutant. We know of none in
  `adler32.c`. The nearest is our own finding F0001, and the file without
  that patch is killed, in `body_adler32_z_null`.

On 2026-11-26 the review of preconditions changed `EmptyBuffer.v`,
`Contract.v`, and `ContractProof.v`. The full run was not repeated. No
mutant was killed by any of those three files, and a mutant is killed by
the first file that fails, so the 521 are killed as before. As a check, 93
mutants were run again: the 4 survivors, the file without our patch, and
every mutant in the first part of `adler32_z`. The same 4 survive and the
other 83 that compile are killed.

Later that day the proofs for the functions with ticks were added, which
are five more files a mutant has to pass. The same 93 were run again, with
the same result. The 4 survivors pass the proofs with ticks too, as they
must: two are the same program, and two change a value the contracts do
not fix. None of them changes how many ticks are spent.

After that the full run was repeated, twice, against every proof as it
then stood. Each of the 624 mutants came out as on 2026-11-25: the same
outcome, the same file that fails first, the same lemma. The first of the
two runs took 157 minutes, with 8 mutants checked at a time. The tool
compiles first the files that name the function a mutant changes.
`WholeFile.v`, added that day, names every function and requires nearly
every file, so nothing was put first any more, and each mutant of a
combine function waited for the proofs of `adler32_z`. The order was
changed: the first file that names a changed function now comes after the
files it requires and no others. The second run, with that change and 14
at a time, took 46 minutes. The order decides only how long a run takes.
A mutant survives only if every file compiles.

To repeat the run, after `make check` and `make proofs`:

```
tools/in-container.sh make mutants JOBS=14
```

`JOBS` is how many mutants are checked at a time. Without it, half the
processors are used. Four full runs on the same 16 processors gave the
same result for every mutant. The three with 14 at a time and a working
build order took 24, 50, and 46 minutes. We have not looked into the
difference. It is not part of `make full`.
The full list, one line per mutant, is written to
`build/mutants/adler32/report.txt`.

## How the proof is organized

| File | Contents |
|---|---|
| `Model.v` | The mathematics. The C code adds bytes into two accumulators and reduces modulo 65521 only now and then. This file relates that to the specification, which reduces at every step. No C, no separation logic. |
| `Bridge.v` | What each machine operation the code uses does, in terms of mathematical integers. |
| `Steps.v` | One unrolled step of the C loop, in terms of the model. |
| `Buffer.v` | Splitting and rejoining a byte buffer at a moving pointer. |
| `Spec.v` | The narrower contracts for a null and for a non-empty buffer. |
| `Verif.v` | The proofs for `adler32_z`. |
| `VerifWrapper.v` | The proofs for `adler32`. |
| `EmptyBuffer.v` | The contracts and proofs for a buffer of length zero. |
| `Contract.v` | The single contract of `adler32_z` and of `adler32`. Definitions only. |
| `ContractProof.v` | The derivation of those contracts from the narrower ones, and the proofs that the narrower ones follow from them. |
| `ContractReview.v` | Checked statements that back the review of preconditions. |
| `AxiomAudit.v` | Every proven result, with what it depends on printed for the axiom check. |
| `Combine.v` | The contracts and proofs for the combine functions. |
| `CensusAdler32.v` | The census for this file, pinned as checked statements. |
| `CombineGuarded.v` | The proof that closes the one open census item. |
| `Ticked.v` | The five functions with ticks added, computed, and the checks that removing the ticks gives back the originals. |
| `CostContract.v` | The contracts with a cost bound, written out and generated. Definitions only. |
| `VerifTicked.v` | The proofs for `adler32_z` with ticks, one for each kind of buffer argument. |
| `CombineTicked.v` | The proofs for the combine functions with ticks. |
| `CostContractProof.v` | The single contract with ticks of `adler32_z` and of `adler32`, the proofs that written and generated contracts say the same, and the `two_forms` lemmas. |
| `WholeFile.v` | One statement for the whole file: every function it defines meets its contract. The claim in `claims/adler32.md` names it. A second statement says the same of the functions with ticks. |

Three points about the argument:

1. **The accumulators cannot overflow.** `Model.v` bounds them after at most
   5552 bytes, far below 2^64.
2. **Reducing late gives the same answer as reducing at every step.** This
   is `modpair_acc`, which rests on a Layer 1 lemma.
3. **The one-byte path is exact only for a reduced checksum.** It reduces
   with a single conditional subtraction. For the second accumulator that is
   exact only when the high half of the incoming checksum is already below
   65521. Every genuine running checksum meets that condition, which is why
   the contract is stated against the Layer 2 specification and not as an
   exact value for every input.

Two points about the combine functions:

1. **The formula avoids division.** The code adds 65521 to keep values
   non-negative, then subtracts 65521, or twice 65521, a fixed number of
   times. `Model.v` proves that this equals a true reduction for the ranges
   that arise, and that the result is the closed form for the checksum of a
   concatenation that Layer 1 proves.
2. **A negative length returns early.** The specification allows any result
   there, as the manual says, so that branch needs no arithmetic.

## Building

At the top of the repository, with the pinned toolchain active:

```
make check
make -C proofs/adler32
```

The second command takes about five minutes.
