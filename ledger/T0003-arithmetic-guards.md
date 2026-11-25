# T0003: Removing arithmetic guards preserves behavior

| Field | Value |
|---|---|
| Kind | Transformation obligation |
| Status | Unproven. Anything that relies on it rests on it as a stated assumption. |
| Recorded | 2026-11-24 |

## The transformation

Guard.v in proofs/lib puts a test for the bad operand values in front of each statement that contains an open census item, with a jump to a missing label when the test succeeds.

## The obligation

If the guarded program never gets stuck, the original program takes the same steps apart from the tests, and at each guarded statement the operands are outside the tested range.

## What relies on it

The claim that the signed remainder in the internal Adler-32 combine function never sees a negative operand, in proofs/adler32/CombineGuarded.v.

## Evidence so far

The guarded function is proven in VST against the same contract as the plain one. Erasing the guard gives back the original function body exactly, checked by computation. The functions with no open item are left unchanged, also checked.

## What a proof would take

A simulation between two Clight programs with equal memories, since guards touch no memory and assign no variable. The simplest of the three. Estimated at a few hundred lines.
