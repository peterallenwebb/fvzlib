# Proofs of the Adler-32 C contracts

Layers 3 and 4 for `adler32.c` of patched zlib 1.4: the C contracts and the
VST proofs that the code meets them.

Checked on 2026-11-25 on the project's first target, x86-64 Linux, in the
toolchain container, with Rocq 9.2.0, CompCert 3.18, and VST 2.17. They were
first checked on 2026-11-24 on an ARM Mac and carried over with no change to
any proof script. `make full` at the top of the repository runs them.
`make check` does not, because they need VST.

## What is proven

The functions proven are the real ones from the patched tree, with no
instrumentation and no transformation. `adler32.c` contains no goto, so the
contracts attach directly to the code that ships.

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
and the internal function that both combine functions call.

"Satisfies the Layer 2 specification" means, for `adler32_z` and `adler32`:
if the checksum argument is the Adler-32 checksum of some earlier bytes, the
result is the Adler-32 checksum of those bytes followed by the buffer, as RFC
1950 defines it. For the combine functions it means: if the two arguments
are the checksums of two byte sequences and the length is that of the
second, the result is the checksum of the two sequences joined.

All nine proofs rest on VST's standard axioms only.

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

For no bytes, the Layer 2 specification says a genuine running checksum
comes back as it went in. The code returns the two halves of its argument,
each reduced modulo 65521, which is the same value for every genuine
checksum.

One call that C allows is outside this contract: a pointer to an allocation
of size zero, such as some implementations return from `malloc(0)`.
CompCert's memory model has no position in such a block that it accepts in
a comparison, so VST cannot prove anything about that call.

## What is not proven here

- **A zero-length buffer in an allocation of size zero.** See above.
- **A 32-bit range for the combine functions.** Their contract does not
  promise that the result fits in 32 bits. For arguments that are not
  checksums it need not, and the manual promises nothing for those.
- **Cost.** These contracts have no cost clause. Cost bounds for `adler32_z`
  and `adler32` are proven separately, for instrumented code, in
  `spikes/termination`.
- **One contract per function.** `adler32_z` and `adler32` each have three
  contracts here, one for each case. They are not yet combined into a single
  contract. The non-empty contract also still describes the buffer as a
  whole array, not as a run of bytes inside a larger one.
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
"the original never takes a remainder of a negative value" rests on an
unproven obligation, recorded in the ledger as T0003.

## The patch matters

The null-buffer proof goes through only for the patched source. Against
pristine zlib 1.4 it fails at the one-byte path, where VST asks for memory
at the null pointer. That is finding F0001, seen from the proof's side.

## How the proof is organized

| File | Contents |
|---|---|
| `Model.v` | The mathematics. The C code adds bytes into two accumulators and reduces modulo 65521 only now and then. This file relates that to the specification, which reduces at every step. No C, no separation logic. |
| `Bridge.v` | What each machine operation the code uses does, in terms of mathematical integers. |
| `Steps.v` | One unrolled step of the C loop, in terms of the model. |
| `Buffer.v` | Splitting and rejoining a byte buffer at a moving pointer. |
| `Spec.v` | The contracts. |
| `Verif.v` | The proofs for `adler32_z`. |
| `VerifWrapper.v` | The proofs for `adler32`. |
| `EmptyBuffer.v` | The contracts and proofs for a buffer of length zero. |
| `Combine.v` | The contracts and proofs for the combine functions. |
| `CensusAdler32.v` | The census for this file, pinned as checked statements. |
| `CombineGuarded.v` | The proof that closes the one open census item. |

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

The second command takes about two minutes.
