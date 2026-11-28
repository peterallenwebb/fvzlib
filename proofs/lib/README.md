# Analyses and transformations over the syntax tree

Rocq functions over Clight syntax trees that the proofs share, and the
general theorems about them. The first four files compute and prove nothing
by themselves. The last three are theorems about any program.

| File | Contents |
|---|---|
| `Census.v` | Lists the arithmetic in a function that VST does not check |
| `Guard.v` | Inserts a test in front of each open census item, so that a VST proof has to show the bad operand values never arise |
| `Ticks.v` | Adds a counter that is spent on entry to a function and at the start of each loop iteration, and removes it again |
| `TickLogic.v` | How a VST contract speaks of that counter, and `with_ticks`, which makes the form with ticks of a contract. Needs VST and proves nothing about a program. |
| `Executions.v` | What it means for a program never to go wrong, in CompCert's terms. Two definitions and a lemma. |
| `Soundness.v` | `verified_program_never_goes_wrong`: a program VST has verified never goes wrong in CompCert's semantics. Applies VST's soundness theorem and adds what it does not give. |
| `GuardSound.v` | `guards_removed`: if a program with guards never goes wrong, then in the program without them no guard's condition ever holds. Ledger entry T0003. Needs CompCert only. |

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

What a proof about the guarded program says of the program without the
guards is `guards_removed`, in `GuardSound.v`. It was recorded in the
ledger as the obligation T0003 and proven on 2026-11-27. If the guarded
program never goes wrong, the original passes through matching states, and
in each of them every test for the statement about to run evaluates to
false. It does not show that the original itself never goes wrong. See the
[ledger entry](../../ledger/T0003-arithmetic-guards.md).

## From VST's logic to executions

A VST proof is a statement in VST's logic. `Soundness.v` takes a whole
program that VST has verified to a statement in CompCert's own terms: no
behavior of the program is a wrong one. That is the premise of CompCert's
theorem about the code it compiles, and of our theorems about
transformations.

VST's soundness theorem does not give this as it stands. Four things are
added, and each shows in the statement or in what it depends on.

- **A hypothesis VST's theorem takes and does not prove.** An external
  call that may be expanded inline behaves the same on a memory that
  grants more permissions.
- **A hypothesis of ours.** Such a call has one result. VST's theorem says
  some execution is safe, CompCert asks it of every execution, and the two
  agree only where a step has one outcome.
- **That `main` returns an integer.** CompCert calls a program finished
  when `main` returns an integer. VST calls it finished when `main` returns
  anything. `main_returns_an_int` closes the difference for a `main` with
  no loop and no jump, and with a `return` of a value on every path. It
  holds where pointers have 64 bits.
- **That VST's copy of the step relation agrees with CompCert's.**

VST's theorem also depends on two axioms beyond the six the contract
proofs use, and VST's own bridge from the proofs its tactics build adds a
third. They are in `audit/execution-axioms.txt`.

The result is about whole programs. A library has no `main`, so it is used
through a client: see [proofs/adler32_client](../adler32_client/README.md).

## The ticks

`Ticks.v` adds a counter to a function. One tick is spent on entry and one
at the start of every loop iteration. A tick with the counter at zero jumps
to a label that does not exist, which is a stuck state, so a VST proof about
the function with ticks shows that the counter never runs out. `erase_ticks`
removes the counter again.

`TickLogic.v` is the other half. `ticks gv t` says the counter holds `t`.
`with_ticks` takes the precondition and postcondition of a contract and a
cost, and gives the contract's form with ticks: the same precondition with a
counter holding at least the cost beside it, and the same postcondition with
the counter holding what was not spent. A contract and its form with ticks
therefore differ in the counter and in nothing else.

The instrumentation began in the contract transfer spike and moved here on
2026-11-26, when the Adler-32 proofs came to depend on it. What a proof
about a function with ticks implies for the function without them rests on
two theorems, stated in `spikes/transfer/TickStatements.v`. One is proven.
The other is ledger entry T0002.

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
