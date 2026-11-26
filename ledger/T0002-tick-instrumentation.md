# T0002: Bounded ticks bound the steps, and erasing the ticks preserves behavior

| Field | Value |
|---|---|
| Kind | Transformation obligation |
| Status | Two statements. The first is proven. The second is stated in Rocq and unproven. Anything that relies on the second rests on it as a stated assumption. |
| Recorded | 2026-11-24 |
| Updated | 2026-11-25: both statements written in Rocq, the first proven. 2026-11-26: what relies on it |

## The transformation

Ticks.v in proofs/lib adds a counter that is spent on function entry and at the start of each loop iteration, with a jump to a missing label when it runs out.

## The obligation

Two statements. Both are written out in spikes/transfer/TickStatements.v, in terms of CompCert's semantics of Clight. Each is a definition of a proposition, not an axiom, so stating it assumes nothing.

### First: bounded ticks bound the steps

`bounded_ticks_bound_steps`. Take a program in which every function is instrumented and has a body of size at most K. Start any of its functions with an empty continuation. An execution that has spent c ticks has taken at most K times (c + 1), plus 2, steps.

**Status: proven**, on 2026-11-25, in spikes/transfer/TickBound.v, as `bounded_ticks_bound_steps_holds`. The file is 477 lines. The proof adds no axiom to the ones the statement already mentions through CompCert's semantics. It holds for either of CompCert's two rules for entering a function.

Its limits:

- A step is a step of CompCert's semantics of Clight, not a machine instruction. A call to an external function is one step, whatever that function does.
- Every function of the program must be instrumented, and none may contain a jump or a label. A function with a goto must have it removed first, which is obligation T0001.
- It counts ticks spent. It does not say how many ticks an execution spends. That comes from the cost contracts, which are statements in VST's logic about the value of the counter. Joining the two needs VST's soundness theorem and has not been done.
- It is about the instrumented program. Reaching the program without ticks needs the second statement.

### Second: erasing the ticks preserves behavior

`erasure_preserves_behavior`. Take a program that does not use the three names the instrumentation adds, and instrument it with any budget. If the instrumented program never goes wrong, every behavior of the original program is a behavior of the instrumented one. A behavior is CompCert's: the trace of events, and whether the execution terminates, with which value, runs forever, or goes wrong.

**Status: stated, unproven.** No proof has been attempted, so the statement itself has not been tested by one. It may need more side conditions than it has.

Its limits as stated:

- It is about whole programs.
- It does not cover a client that sets the counter again between calls. `instrument_program` does not add such assignments.

## What relies on it

The cost bounds for all five functions of adler32.c. Since 2026-11-26 they are part of the contracts with ticks in proofs/adler32/CostContract.v, proven for the instrumented functions. Without the second statement those bounds are bounds on instrumented code only.

The claim for adler32.c, in claims/adler32.md, does not rely on this entry, because it says nothing about cost.

## Evidence so far

Contracts that cover memory safety, the value returned, and the cost are proven in VST for the instrumented functions of adler32.c. Erasing the ticks gives back the original function bodies exactly, checked by computation. The five instrumented functions have the form the first statement asks for, checked in spikes/termination/adler32_bound.v, and the largest has size 689.

## What a proof of the second statement would take

A simulation across memories that differ by one block, estimated at one to two thousand lines, with CompCert's proof for its local variable simplification pass as the model.
