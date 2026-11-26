# Spike: contract transfer

Run on 2026-11-24 on the development machine, an ARM Mac, with Rocq 9.2.0,
CompCert 3.18, and VST 2.17. Run again on 2026-11-25 on the project's first
target, x86-64 Linux, in the toolchain container, where every file checks.
Exploratory. Not part of the main build.

## The question

Two of our decisions transform the Clight syntax tree before proving
anything: removing forward gotos, and adding a tick counter. VST then proves
a contract for the transformed function. The question was whether that
contract can be carried back to the original function.

## The answer

**No, not as a VST contract.** A function with a reachable goto has no VST
contract at all, so there is nothing to carry a contract back to.

This follows from a lemma VST itself proves, `semax_Sgoto_inv`: any proof of
a triple for `goto l` has a precondition that entails falsehood. The reason
is in VST's definition of its judgment. A triple for a statement must hold
inside every enclosing function, and what a goto does depends on which
function encloses it.

**What can be carried back is a statement about executions.** VST's
soundness theorem turns a verified program into a statement in terms of
CompCert's semantics: the program never gets stuck. A behavior-preservation
theorem for our transformations, also stated in CompCert's semantics, can
then carry that statement from the transformed program to the original. This
is the fallback the README anticipated.

## What the spike built

| File | Contents | Result |
|---|---|---|
| `toy.c` | A function with a loop and a forward goto to cleanup code that stores and returns | |
| `GotoElim.v` | The goto transformation, with its side conditions | Computes |
| `toy_nogoto.v` | The transformation applied to the toy | The result is goto-free |
| `verif_toy_nogoto.v` | A VST contract for the transformed toy | Proven |
| `Ticks.v` | The tick instrumentation and its erasure | Computes |
| `toy_ticked.v` | The instrumentation applied to the transformed toy | Erasure gives back the input exactly |
| `verif_toy_ticked.v` | A VST cost contract for the instrumented toy | Proven |
| `Transfer.v` | Where the goto goes in CompCert's semantics | Proven, no axioms |
| `TickStatements.v` | The two theorems about ticks, stated against CompCert's semantics. Added 2026-11-25 | Definitions only |
| `TickBound.v` | The first of the two: bounded ticks bound the steps. Added 2026-11-25 | Proven |

The two VST proofs rest on VST's standard axioms only.

## Findings

1. **The proof-side workflow works for both transformations.** The
   transformed toy and the instrumented toy each have a proven contract. The
   proofs take 45 and 60 lines and check in about 7 seconds each.
2. **The tick overhead in a proof is small.** One tactic steps through a
   tick. Each invariant gains one conjunct for the counter. The branch that
   jumps to the missing label is closed by contradiction, since it is
   reached only when the counter is zero.
3. **A jump to a missing label is a usable "stuck" statement.** It is stuck
   in CompCert's semantics, and VST can prove it only when unreachable.
4. **In Clight a label covers one statement.** The cleanup code is the
   labeled statement together with the statements after it in the enclosing
   sequence. `Transfer.v` confirms that this is the code CompCert's semantics
   runs after the jump, under the continuation of the enclosing call.
5. **Goto-free functions need no transfer for their functional contract.**
   Twelve of the fifteen library files, including `adler32.c`, have no goto.
   Their contracts can be proven directly on the real code. Only the cost
   contract needs the instrumented copy.

## What this means for downstream verifiers

They are not left without contracts. They import the contracts of the
transformed functions, verify their own code against them in VST, and apply
our behavior-preservation theorem to their final whole-program result. What
they cannot have is a VST contract attached to the untransformed text of a
function that contains a goto.

## The two theorems about ticks

Added on 2026-11-25. The ledger entry is
[T0002](../../ledger/T0002-tick-instrumentation.md).

`TickStatements.v` states both in Rocq. Each is a definition of a
proposition, so stating it assumes nothing.

**Bounded ticks bound the steps: proven.** Take a program in which every
function is instrumented and has a body of size at most `K`. Start any of
its functions. An execution that has spent `c` ticks has taken at most
`K * (c + 1) + 2` steps. `TickBound.v` proves it.

The proof gives each state a number, its potential. Every step lowers the
potential, except entering a loop body or a function, which raises it by
less than `K`. Each such step is followed at once by a tick, and no other
can happen until that tick is spent. So each rise is paid for by one tick.
The proof never looks at memory or at the value of the counter.

Its limits:

- **Steps of CompCert's semantics.** Not machine instructions. A call to an
  external function is one step, whatever that function does.
- **Every function instrumented, and no jumps.** A function with a goto
  must have it removed first.
- **It counts ticks spent.** How many an execution spends comes from the
  cost contracts, which are statements in VST's logic. Joining the two
  needs VST's soundness theorem and is not done.
- **What it rests on.** `Print Assumptions` lists four of the six allowed
  axioms, and two parameters of CompCert's semantics: what an external
  function does and what inline assembly does. The statement alone, before
  any proof, already lists the same four and two, because it speaks of
  CompCert's semantics. The proof adds none. The two parameters are not
  assumptions, and
  [audit/semantics-parameters.txt](../../audit/semantics-parameters.txt)
  says why.

**Erasing the ticks preserves behavior: stated, not proven.** Take a
program that does not use the names the instrumentation adds, and
instrument it. If the instrumented program never goes wrong, every behavior
of the original is a behavior of the instrumented one. No proof has been
attempted, so the statement has not been tested by one and may need more
side conditions. It does not cover a client that sets the counter again
between calls.

## Open problems the spike exposed

1. **The behavior-preservation theorems are not proven.** The one for
   ticks is now stated in Rocq, in `TickStatements.v`. The one for goto is
   still stated only in prose. Each is a
   simulation between two Clight programs, in the style of a CompCert
   compiler pass. For the goto transformation the side conditions are
   already written in `GotoElim.v`: the cleanup code must contain no jump,
   label, break, or continue, and must return on every path.
2. **The counter changes the program's memory.** The instrumented program
   has one more global than the original, so the two run with different
   memory layouts. The erasure theorem then needs an argument about related
   memories, which is much heavier than one about equal memories. Keeping the
   counter out of memory would avoid this and should be evaluated.
3. **A fixed counter bounds total work, not work per call.** A client that
   calls the library an unbounded number of times needs the counter refilled.
   Setting the counter at each call site is one option. It needs designing.
4. **VST's lemma could not be restated in this spike.** `semax_Sgoto_inv`
   sits in a module VST does not export under a usable name. `Transfer.v`
   quotes it. Re-proving it against the exported judgment is a small task.

Problems 2 and 3 belong to the planned termination spike on Adler-32.
