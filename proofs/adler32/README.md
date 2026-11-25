# Proofs of the Adler-32 C contracts

Layers 3 and 4 for `adler32.c` of patched zlib 1.4: the C contracts and the
VST proofs that the code meets them.

Checked on 2026-11-24 on the development machine, an ARM Mac, with Rocq
9.2.0, CompCert 3.18, and VST 2.17. The project's first target is x86-64
Linux. The C types involved are the same there, so these proofs are expected
to carry over, but they have not been checked on that target. Until they
are, they are not part of `make check` at the top of the repository.

## What is proven

The functions proven are the real ones from the patched tree, with no
instrumentation and no transformation. `adler32.c` contains no goto, so the
contracts attach directly to the code that ships.

| Function | Case | Proven |
|---|---|---|
| `adler32_z` | Null buffer, any length | Returns a value satisfying the Layer 2 specification, which is the initial value 1 |
| `adler32_z` | Non-null, non-empty buffer, any 64-bit checksum argument | Memory safe, buffer unchanged, result below 2^32, and result satisfies the Layer 2 specification |
| `adler32` | Null buffer, any length | As for `adler32_z` |
| `adler32` | Non-null, non-empty buffer | As for `adler32_z` |

"Satisfies the Layer 2 specification" means: if the checksum argument is the
Adler-32 checksum of some earlier bytes, the result is the Adler-32 checksum
of those bytes followed by the buffer, as RFC 1950 defines it.

All four proofs rest on VST's standard axioms only.

## What is not proven here

- **A non-null buffer of length zero.** It needs the more general buffer
  description from the Layer 3 design, in which the buffer is a run of bytes
  inside a non-empty array.
- **The combine functions.** `adler32_combine` and `adler32_combine64` are
  not started.
- **Cost.** These contracts have no cost clause. Cost bounds for `adler32_z`
  and `adler32` are proven separately, for instrumented code, in
  `spikes/termination`.
- **One contract per function.** Each function has two contracts here, one
  for each case. They are not yet combined into a single contract.
- **The gap VST leaves.** The listing of unchecked arithmetic constructs,
  and the extra obligations it calls for, are not done.

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

## Building

At the top of the repository, with the pinned toolchain active:

```
make check
make -C proofs/adler32
```

The second command takes about two minutes.
