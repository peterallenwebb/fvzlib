# T0003: Removing arithmetic guards preserves behavior

| Field | Value |
|---|---|
| Kind | Transformation obligation |
| Status | Proven on 2026-11-27, as `guards_removed` in proofs/lib/GuardSound.v. One part of what its title suggests is not in the theorem: see "What is not proven". |
| Recorded | 2026-11-24 |

## The transformation

Guard.v in proofs/lib puts a test for the bad operand values in front of each statement that contains an open census item, with a jump to a missing label when the test succeeds.

## The obligation

If the guarded program never gets stuck, the original program takes the same steps apart from the tests, and at each guarded statement the operands are outside the tested range.

## The theorem

`guards_removed`, in proofs/lib/GuardSound.v. It is stated in CompCert's semantics of Clight and is about any program.

Let `p'` be what the transformation makes of the program `p`. Let `p'` use the guards' label nowhere else, which a computed check decides. Let `p'` never go wrong. Then for every state an execution of `p` passes through:

- **The same steps.** An execution of `p'` passes through a matching state: the same memory, the same variables, the same statement apart from the tests, the same stack of calls.
- **No test's condition holds.** In that state of `p`, every test the transformation would put in front of the statement about to run evaluates, and evaluates to false.

The proof is a simulation, as was expected when the obligation was recorded. `p'` follows each step of `p` by first running the tests in front of its statement, then taking the same step. Its safety is what gets it past the tests: a test has to evaluate, since `p'` is not stuck there, and has to come out false, since the jump it would make is stuck.

The file is 888 lines. The estimate was a few hundred.

## What is not proven

- **That the original never goes wrong.** The theorem carries facts from the guarded program to the original. It does not show that the original cannot get stuck. That needs the other direction too: that the original can take every step the guarded program takes. It has not been attempted. For `adler32.c` it is not needed, since the functions without guards are verified directly.
- **That the two programs have the same behaviors.** For the same reason.
- **Guards for all four kinds of item.** The transformation implements guards for signed division and remainder and for right shifts of signed values. For left shifts and conversions it refuses, and the theorem is about what it does produce.

## What it rests on

Four of the six axioms the contract proofs use: excluded middle, functional extensionality, and the two behind the real numbers. And two axioms of CompCert about external functions and inline assembly, `Events.external_functions_properties` and `Events.inline_assembly_properties`, which are in audit/execution-axioms.txt. Excluded middle is used by the proof itself, to go from "never goes wrong" to "can step or has finished". The others come with CompCert's libraries. It does not use VST.

Its premise, that the guarded program never goes wrong, comes from VST through proofs/lib/Soundness.v, which adds two hypotheses about external calls. That path brings in three more axioms.

## What relies on it

The claim that the signed remainder in the internal Adler-32 combine function never sees a negative operand. For the client program in proofs/adler32_client it is now a theorem about the function as written: `remainder_operand_not_negative`, in proofs/adler32_client/Guarded.v. Whenever that program is about to run `len2 %= BASE`, `len2` holds a 64-bit integer that is not negative.

Like every statement about executions, it is about a whole program. It is shown for that one program. For another caller the same two theorems apply, once that caller is verified.

## Evidence beside the theorem

The guarded function is proven in VST against the same contract as the plain one. The transformation applied to the whole client program gives exactly the client with that one function replaced, checked by computation. So `main` and the other four functions have nothing to guard.
