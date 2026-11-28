# A whole program that calls `adler32.c`

Written 2026-11-27.

The proofs in [proofs/adler32](../adler32/README.md) are statements in
VST's logic, one function at a time. This directory takes them to
statements about how a program runs, in CompCert's semantics. A library
does not run by itself, so it does that for one whole program.

Nothing here is a claim about zlib. `client.c` is ours.

## What is proven

For the program `client.c`, on the project's first target, x86-64 Linux:

1. **It never goes wrong.** `client_never_goes_wrong`, in `Client.v`. No
   behavior of the program, in CompCert's semantics of Clight, is a wrong
   one: it starts, and it never reaches a state that is stuck.
2. **The remainder in the internal combine function never sees a negative
   operand.** `remainder_operand_not_negative`, in `Guarded.v`. Whenever
   the program is about to run `len2 %= BASE`, `len2` holds a 64-bit
   integer that is not negative. This is about the function as zlib ships
   it, with no test added.

Both hold under two hypotheses about external calls, which are in the
statements. See "What they rest on".

## The program

`main` writes nine bytes into a local array and makes seven calls:

| Call | What it exercises |
|---|---|
| `adler32(0L, Z_NULL, 0)` | A null buffer |
| `adler32(start, data, 9)` | A whole buffer |
| `adler32_z(start, data, 9)` | The same, through the other function |
| `adler32(start, data, 4)` | The first four bytes of a larger array |
| `adler32(start, data + 4, 5)` | The last five, at a pointer into it |
| `adler32_combine(first, second, 5)` | The two checksums combined |
| `adler32_combine64(first, second, 5)` | The same, through the other function |

The two combine functions call the internal one, so all five functions of
`adler32.c` run.

`client.c` includes `adler32.c`. It does not link against it. That gives
one Clight program, which is what the theorems speak of. `Client.v` checks
that each of the five functions comes out of that translation as exactly
the syntax tree the contracts are proven for.

## How the result is reached

| File | Contents |
|---|---|
| `client.c` | The program |
| `Client.v` | The five functions are the same ones. `main` meets its contract. The whole program is verified in VST. It never goes wrong. |
| `Guarded.v` | The client with the guarded form of the internal combine function is verified and never goes wrong. So in the client as written no test's condition holds, and the remainder's operand is not negative. |
| `AxiomAudit.v` | Every result, with what it depends on printed for the axiom check |

The general theorems are in [proofs/lib](../lib/README.md):
`verified_program_never_goes_wrong` in `Soundness.v`, and `guards_removed`
in `GuardSound.v`. They are about any program. This directory applies
them.

The proof of `main` uses only the contracts of the functions it calls.
Each call has to meet its callee's precondition, so the proof is also a
check that a caller can meet the contracts as written: with a null buffer,
with a whole array, and with a run of bytes inside a larger array.

## What they rest on

- **Two hypotheses about external calls.** `more_permission_same_call` is
  taken by VST's soundness theorem, and VST does not prove it.
  `inline_calls_deterministic` is ours: VST's theorem says that some
  execution is safe, CompCert asks it of every execution, and the two
  agree only where each step has one outcome. Both are about calls to
  built-in and external functions. This program makes none, but the
  theorems it uses are about all programs.
- **Eleven axioms.** The six the contract proofs use, and the five in
  [audit/execution-axioms.txt](../../audit/execution-axioms.txt), which
  come with VST's soundness theorem and CompCert's semantics. The build
  checks every result here against those two lists.
- **A `main` of a simple shape.** No loop, no jump, and a `return` of a
  value on every path. It is what lets us show that `main` returns an
  integer, which CompCert requires of a finished program and VST's theorem
  does not give.
- **Pointers of 64 bits.** Used in the same place.

## Limits

- **One program.** Seven calls, nine bytes. Nothing here says what another
  caller does. For another caller the same general theorems apply, once
  that caller is verified.
- **Safety only.** The statement about executions is that the program does
  not get stuck. What the functions return is in their contracts, and the
  proof of `main` uses it, but no returned value appears in the final
  theorem. `main` returns 0 whatever the checksums are.
- **One translation unit.** Nothing here is about linking separately
  compiled files.
- **No cost.** The contracts with a cost bound are not carried to
  executions. There is still no theorem that a call terminates.
- **CompCert's semantics of Clight.** Not ISO C, and not the code gcc
  produces.
- **Not shown from the guarded program alone: that the original is safe.**
  `guards_removed` carries facts from the guarded program to the original.
  That the original never goes wrong is proven separately, from the
  contracts of the functions without guards.

## One thing about the tools

A first version of `client.c` named two local variables `joined` and
`joined64`. VST's tactic for a function call did not finish, in several
minutes, on the call whose result went to `joined64`. Every stage of the
tactic that we timed separately was fast. With the variables renamed to
`both` and `wide` the same call takes a fraction of a second. We have not
found the cause. If a proof step that should be instant does not return,
try renaming the variable.

## Building

At the top of the repository, in the toolchain container, after
`make check` and `make -C proofs/adler32`:

```
make -C proofs/adler32_client
```

It takes under a minute. `make full` runs it.
