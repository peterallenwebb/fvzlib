# T0001: Removing forward gotos preserves behavior

| Field | Value |
|---|---|
| Kind | Transformation obligation |
| Status | Unproven. Anything that relies on it rests on it as a stated assumption. |
| Recorded | 2026-11-24 |

## The transformation

GotoElim.v in spikes/transfer replaces each forward goto to a cleanup label by a copy of the cleanup code, under side conditions it checks: the cleanup code contains no jump, label, break, or continue, and returns on every path.

## The obligation

If the transformed program never gets stuck, the original program takes corresponding steps and has the same observable behavior.

## What relies on it

Nothing yet. It will be relied on for inflate.c, infback.c, and inffast.c.

## Evidence so far

The transformation is applied to a toy function and a VST contract is proven for the result. Transfer.v proves, for that toy, that CompCert's semantics sends the goto to exactly the code the transformation copies.

## What a proof would take

A simulation between two Clight programs with equal memories, in the style of a CompCert compiler pass. Estimated at several hundred lines.
