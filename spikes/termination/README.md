# Spike: termination and cost for the Adler-32 functions

Run on 2026-11-24 on the development machine, an ARM Mac, with Rocq 9.2.0,
CompCert 3.18, and VST 2.17. Run again on 2026-11-25 on the project's first
target, x86-64 Linux, in the toolchain container, where every file checks.
Exploratory. Not part of the main build.

On 2026-11-26 the main proofs took over what this spike began. In
`proofs/adler32`, each of the five functions with ticks is proven to meet
one contract that covers memory safety, the value returned, and the cost
bound, for every call including a null buffer and a buffer of length zero.
The instrumentation moved to `proofs/lib/Ticks.v`.

On 2026-11-27 the spike's own files were retired. Its cost proofs were
superseded: their contracts said less, cost and memory safety only, for a
buffer that is not null and not empty. They are removed from the tree and
remain in the history, last at commit `fb039b0`. Two things were not
superseded, and are kept:

- **The step bound for this file's functions** moved to
  `proofs/adler32/StepBound.v`, rebased on the functions with ticks of the
  main proofs.
- **The client that refills the counter** stays here, as `Twice.v`. It is
  the one experiment left in this directory. It is now proven against the
  contract of `adler32_z` with ticks from the main proofs.

The rest of this file is the record of the spike as it was run. Where it
names a file that is gone, the "Files" section at the end says where the
result is now.

## The question

Can the tick counter give a proven cost bound for real zlib code, and what
is still needed to turn that into a statement that the original code
terminates?

## What was proven

All the results are VST contracts for instrumented code and rest on VST's
standard axioms only.

| Function | Code | Contract |
|---|---|---|
| `adler32_z` | The real function of patched zlib 1.4, with ticks added | Memory safe, buffer untouched, and at most `len/5552 + len/16 + 19` ticks |
| `adler32` | The real function, with ticks added | At most one tick more than `adler32_z` |
| `twice` | A small client that calls `adler32_z` twice and sets the counter before each call | Needs no tick budget from its own caller |
| Internal combine function | The real function, with ticks added | Memory safe and at most 1 tick, for any arguments |
| `adler32_combine`, `adler32_combine64` | The real functions, with ticks added | Memory safe and at most 2 ticks, for any arguments |

The combine functions were added on 2026-11-25. They have no loop, so each
costs one tick for each function entered. The bound of 2 is the one the
Layer 3 design note proposed.

The instrumentation was applied to all five functions of `adler32.c`.
Erasing the ticks gives back the original function bodies exactly, which the
build checks by computation.

## Limits of these results

- **Cost and memory safety only.** The contracts say nothing about the value
  returned. The functional proof is separate work.
- **A non-null, non-empty buffer.** The null buffer and the zero-length
  buffer are not covered here.
- **Instrumented code.** These are contracts for the code with ticks. What
  they imply for the original code depends on the two theorems below.
- **The target.** The proofs were written against the syntax tree from
  CompCert built for ARM macOS. They pass unchanged against the tree for
  x86-64 Linux.

## Findings

1. **The cost bound in the design note was off by three.** The note proposed
   `len/5552 + len/16 + 16`. The proven bound is `len/5552 + len/16 + 19`.
   Each loop spends a tick on its final, failing test, which the proposal
   did not count. This is the kind of error a proof exists to catch.
2. **Tick overhead in the proof is small.** The function has six tick
   sites: one on entry and one in each of its five loops. Each costs one
   tactic call. Each loop invariant gains one clause for the counter. Three
   short arithmetic lemmas justify the bound.
3. **The bound follows the structure of the code.** 5552 is 16 times 347,
   so a full block costs one tick for the outer loop and 347 for the inner
   one. The proof tracks the counter exactly through each loop and compares
   with the bound only at the end.
4. **The two sixteen-fold unrolled loops are not a problem.** One tactic
   steps through all sixteen reads. The values of the two running sums are
   forgotten after each read, since this proof makes no claim about them.
5. **Reading through a moving pointer needs one idiom.** The buffer is split
   at the pointer's position before each group of reads and put back
   together after. `Buffer.v` has the lemmas. This will be needed for the
   functional proof too.
6. **Budgets compose through calls.** The contract for `adler32` is proven
   from the contract for `adler32_z`, by passing on what remains of its own
   budget.
7. **Refilling at call sites answers the per-call question.** A client that
   sets the counter to the callee's bound before each call can make any
   number of calls, and needs no budget itself. The bound then applies to
   each call separately.

## The two questions left by the transfer spike

**How is the counter refilled between calls?** By an assignment at each call
site, as in `twice`. That assignment is itself instrumentation, to be erased
along with the ticks.

**Can the counter be kept from changing the program's memory?** Not with the
means VST offers. The alternatives were considered:

| Alternative | Why it does not help |
|---|---|
| The counter as a global variable, as here | Adds a global, so the instrumented and original programs lay out memory differently |
| Ticks as calls to an external function, with the budget held outside memory | The function still needs a global symbol, which also takes a place in memory, and it needs VST's heavier machinery for external calls |
| Ticks as compiler builtins, which need no symbol | VST has no proof rule for builtins |

So the global counter stays, and the erasure theorem has to relate two
programs whose memories differ by one block.

## What is still needed for a claim about the original code

Two theorems. On 2026-11-25 both were stated in Rocq, in
`TickStatements.v`, and the first was proven, in `TickBound.v`. Both are
now in `proofs/lib`. The second is not proven. See
[the transfer spike](../transfer/README.md#the-two-theorems-about-ticks)
and ledger entry T0002. The prose below is as written on 2026-11-24.

`adler32_bound.v` applies the first theorem to this file's code. The five
instrumented functions have the form the theorem asks for, and the largest,
`adler32_z`, has size 689. So in a program made of these functions, an
execution that has spent `c` ticks has taken at most `689 * (c + 1) + 2`
steps. Together with the cost contract that would bound the steps of a call
to `adler32_z` by a linear function of `len`. That last link is not made:
the contract speaks of the counter's value in VST's logic, and the theorem
counts steps of CompCert's semantics.

1. **Bounded ticks bound the steps.** In an instrumented program every loop
   iteration and every function entry spends a tick. Between two ticks, only
   straight-line code runs, and its length is bounded by the size of the
   program text. So an execution that spends at most N ticks takes at most
   K times N plus K steps, for a constant K that depends on the program
   text. The proof is a measure argument on Clight states. Estimated at a
   few hundred lines.
2. **Erasure preserves behavior.** If the instrumented program never gets
   stuck, the original program takes corresponding steps, with memories
   related by an injection that leaves out the counter. This is a simulation
   in the style of a CompCert pass. CompCert's own proof for its local
   variable simplification pass relates Clight programs across differing
   memories in the same way and is the model to follow. Estimated at one to
   two thousand lines. This is the larger risk.

Until the second is proven, a termination claim for the original code
rests on it as a stated assumption.

## Files

One file is left here.

| File | Contents |
|---|---|
| `Twice.v` | The client that refills the counter before each of two calls, proven against the main contract of `adler32_z` with ticks |

Where the rest went. The first column is the spike's file, as named
above.

| File of the spike | Contents | Now |
|---|---|---|
| `adler32_ticked.v` | The five instrumented functions, computed, and the erasure checks | `proofs/adler32/Ticked.v` |
| `Buffer.v` | Splitting and rejoining a byte buffer, and the tick tactics | `proofs/adler32/Buffer.v` and `proofs/lib/TickLogic.v` |
| `verif_adler32_z_cost.v` | The cost contract for `adler32_z` and its proof | `proofs/adler32/CostContract.v`, `VerifTicked.v`, `CostContractProof.v` |
| `verif_adler32_cost.v` | The cost contract for `adler32`, and the refilling client | `proofs/adler32/CostContractProof.v`, and `Twice.v` here |
| `verif_combine_cost.v` | The cost contracts for the three combine functions | `proofs/adler32/CombineTicked.v` |
| `adler32_bound.v` | The step bound for a program made of the five instrumented functions | `proofs/adler32/StepBound.v` |

The tick instrumentation itself is `../../proofs/lib/Ticks.v`. The two
theorems about ticks are in `../../proofs/lib/TickStatements.v` and
`TickBound.v`.
