# Analyses and transformations over the syntax tree

Rocq functions over Clight syntax trees that the proofs share. They compute.
They prove nothing by themselves.

| File | Contents |
|---|---|
| `Census.v` | Lists the arithmetic in a function that VST does not check |
| `Guard.v` | Inserts a test in front of each open census item, so that a VST proof has to show the bad operand values never arise |

## The census

VST checks much of what the C standard leaves undefined, but not all. The
census lists every construct of four kinds:

| Kind | Why it is listed |
|---|---|
| Left shift of a signed value | Undefined if the value is negative or the result does not fit |
| Right shift of a signed value | Implementation-defined if the value is negative |
| Division or remainder of signed values | Implementation-defined in the 1990 standard if either operand is negative |
| Conversion into a signed type that cannot hold every source value | Implementation-defined if the value does not fit |

Conversions include the implicit ones: at assignments to memory, at call
arguments, at returns, and between the operands of an arithmetic operator.

Each item gets a status.

| Status | Meaning |
|---|---|
| Closed by constants | The operands are constants for which the result is defined |
| Closed by types | The operand types rule out the bad values, for example a small unsigned type shifted by a small constant |
| Open | Something else has to show the bad values do not arise |

The list is complete for these four kinds by construction, since it visits
every expression. It is recomputed whenever the source changes, and each
file's listing is pinned as a checked statement, so a change in a new
release shows up as a build failure.

It does not cover other gaps: violations of the aliasing rules, pointer
arithmetic that leaves an object, and dependence on evaluation order.

## The guards

For an open item, `Guard.v` puts a test for the bad operand values in front
of the statement. If the test succeeds the program jumps to a label that
does not exist, which is a stuck state. VST can prove a jump only when it is
unreachable, so a VST proof of the guarded function shows the bad values
never arise.

Guards exist for signed division and remainder and for right shifts of
signed values. For left shifts and conversions the transformation refuses,
so an open item is never skipped silently. Those two kinds are still to do.

The transformation works in two steps. The first decides what to test, by
inspecting types and constants. The second inserts the tests, looking only
at the shape of the statements. Keeping them apart lets the result be
computed with the names in the function left folded, so it stays readable.

That removing the guards does not change the behavior of a program that
never gets stuck is an unproven obligation, recorded in the ledger as T0003.

## A preview for the whole library

The census run over the eleven core files of pristine zlib 1.4, on syntax
trees generated on the development machine. Exploratory. Each cell is the
number found, then the number still open.

| File | Left shift | Right shift | Division | Conversion |
|---|---|---|---|---|
| `adler32.c` | 0, 0 | 0, 0 | 2, 1 | 0, 0 |
| `crc32.c` | 11, 11 | 1, 1 | 0, 0 | 0, 0 |
| `compress.c` | 0, 0 | 0, 0 | 0, 0 | 1, 1 |
| `uncompr.c` | 0, 0 | 0, 0 | 0, 0 | 1, 1 |
| `zutil.c` | 9, 0 | 0, 0 | 0, 0 | 4, 4 |
| `inftrees.c` | 3, 3 | 0, 0 | 0, 0 | 0, 0 |
| `inffast.c` | 0, 0 | 0, 0 | 0, 0 | 0, 0 |
| `inflate.c` | 2, 1 | 2, 2 | 0, 0 | 11, 11 |
| `infback.c` | 0, 0 | 0, 0 | 0, 0 | 2, 2 |
| `trees.c` | 56, 49 | 51, 0 | 1, 1 | 2, 2 |
| `deflate.c` | 5, 5 | 8, 2 | 0, 0 | 3, 3 |
| Total | 86, 69 | 62, 5 | 3, 2 | 24, 24 |

So about 100 items are open across the core of the library. The automatic
rules close all 51 right shifts in `trees.c`, where a small unsigned type is
shifted, and all 9 left shifts in `zutil.c`, where constants are shifted.

An earlier count, made with a script, reported fewer right shifts. It looked
at the type of the result. The census looks at how C promotes the operand,
which is what decides whether the shift is a signed one.
