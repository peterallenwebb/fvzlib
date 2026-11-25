# T0002: Bounded ticks bound the steps, and erasing the ticks preserves behavior

| Field | Value |
|---|---|
| Kind | Transformation obligation |
| Status | Unproven. Anything that relies on it rests on it as a stated assumption. |
| Recorded | 2026-11-24 |

## The transformation

Ticks.v in spikes/transfer adds a counter that is spent on function entry and at the start of each loop iteration, with a jump to a missing label when it runs out.

## The obligation

Two statements. First: an execution of the instrumented program that spends at most N ticks takes at most K times N plus K steps, for a constant K that depends on the program text. Second: if the instrumented program never gets stuck, the original program takes corresponding steps, with memories related by an injection that leaves out the counter.

## What relies on it

The cost bounds for adler32_z and adler32 in spikes/termination. Without these two statements those bounds are bounds on instrumented code only.

## Evidence so far

Cost contracts are proven in VST for the instrumented adler32_z and adler32. Erasing the ticks gives back the original function bodies exactly, checked by computation.

## What a proof would take

The first statement is a measure argument, estimated at a few hundred lines. The second is a simulation across memories that differ by one block, estimated at one to two thousand lines, with CompCert's proof for its local variable simplification pass as the model.
