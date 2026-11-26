# Milestone 1 retrospective

Written 2026-11-26, the day Milestone 1 was closed.

This file looks back at the milestone. It is not a claim and adds no
result. The record of what was done is in the
[README](../../README.md#milestone-1-adler-32-end-to-end), and the claim is
in [claims/adler32.md](../../claims/adler32.md). Where this file gives an
opinion or a recommendation, it says so.

## What the milestone was

Take one source file, `adler32.c`, through every stage of the method. It
was decided on 2026-11-23, worked on from 2026-11-24 to 2026-11-26, and
closed after 21 commits.

- **2026-11-24.** The two specification layers, the first finding and its
  patch, both spikes, and proofs for all five functions. All on the
  development machine, an ARM Mac.
- **2026-11-25.** The move to the x86-64 Linux target in a container,
  continuous integration, the check on axioms, one contract per function,
  mutation testing, the differential test, and the first tick theorem.
- **2026-11-26.** The review of preconditions, the claim, the contracts
  with a cost bound, a full repeat of mutation testing, and the closing.

What it produced, in lines:

| Part | Lines |
|---|---|
| `adler32.c`, with its comments | 164 |
| Specifications, `spec/format` and `spec/api` | 857 |
| Proof files for `adler32.c`, not counting the generated syntax tree | 4138 |
| of which the proofs for the functions with ticks | 1396 |
| of which the proof for the guarded function | 199 |
| Shared transformations, `proofs/lib` | 626 |
| Tools | 2683 |
| The README, the proof README, and the claim | 2493 |

## Did it answer what it was for

The milestone had three purposes. This is our reading of how each came
out.

1. **Test every decision at small scale.** Mostly yes. The toolchain, the
   container, the build check, the layered specification, the patch
   sequence, and the cost contracts were all used on real code and all
   worked. Two decisions were not tested on real code: goto removal, since
   the file has none, and the secondary tools, which were out of scope.
2. **Find out whether a contract proven for transformed code can be carried
   back to the original.** Only in part. We know the form the answer must
   take: a statement about executions of a whole program. Of the four
   theorems that would carry it, one is proven: that bounded ticks bound
   the steps. The three that relate a transformed program to the original
   are not. No theorem of ours yet speaks about an execution of a function
   as shipped. The milestone said this answer was needed
   "before we invest in inflate", and it is not complete.
3. **Move one file to a final state, with a claim someone can check.** Yes.
   The claim exists, its references are checked by the build, and it
   relies on one unproven obligation, which it names.

## What went well

- **The proof attempt found a real defect on the first day.** F0001, a null
  dereference in `adler32` that the manual excludes, came out of the
  simplest file in the library. The patch sequence, the witness test, and
  the "proven after a patch" state all had a real case to handle.
- **The move to the target changed no proof script.** Work that did not
  depend on the platform was done first, and it carried over. The one
  repair was to files that listed target-specific names.
- **One command, two machines.** `make full` passes in the container on
  the laptop and on a hosted runner that builds it from nothing. A run
  takes about eight minutes on the laptop and under thirteen on the
  runner once the image is cached.
- **Checks that enumerate found things that reading had missed.** The
  axiom check found three results whose assumptions had never been
  printed. The review of preconditions found two demands that nothing
  needed, and removing them admitted a call that real code makes.
- **Narrow contracts first, then one contract derived from them.** Proving
  each case against the code and deriving the single contract by
  subsumption, with the converse, was cheap and lost nothing.
- **Limits were written down on the day they appeared.** Closing the
  milestone was a matter of collecting them, not of finding them.
- **Mutation testing is stable.** Four full runs, across two days and a
  large change to the proofs, gave the same result for every mutant.

## What went wrong, and what caught it

Each of these was caught. The point of listing them is how.

- **A generated contract that no call could meet.** The first `with_ticks`
  dropped the arguments of the call. Every written contract implied the
  generated one trivially. Only the converse failed. *Caught by proving
  both directions.*
- **Two preconditions asked for more than the code needs.** The whole array
  had to be initialized and readable, though only the run passed is read.
  *Caught by the review, which asked of each clause whether it was
  needed.*
- **Three results had never had their assumptions printed.** *Caught by
  writing a check that requires every proof of a contract to be listed.*
- **Pinned syntax trees named ARM-only built-in functions.** *Caught by
  the move to the target.*
- **A time-saving rule in the mutation tool stopped working without
  notice.** A file added on the last day named every function, and a full
  run took 157 minutes where earlier ones took under an hour. Part of
  that was running 8 mutants at a time and not 14. The results were
  right. The tool had no test of its own shortcut. *Caught only because
  the full run was repeated before closing.*
- **Two of our own tactics had the same names in two files.** The one
  imported last won, and a proof step did nothing. *Caught by a failing
  proof, after some time lost.*
- **A wall-clock time taken across an interruption was recorded, then
  thrown out.** *Caught by rereading the number.*

## What the milestone did not exercise

Adler-32 was chosen because it is small. These are things inflate has and
`adler32.c` does not, so Milestone 1 gives no evidence about them.

- **A goto in real code.** Only a toy was transformed. `inflate.c` and
  `inffast.c` use goto, and the fast path has backward jumps for which we
  have no transformation yet.
- **State.** No struct, no heap, no global, no function pointer. inflate
  has a stream state, a window, and allocator callbacks.
- **Calls across files.** No function here calls outside the file.
  Nothing is proven about how contracts from two files are put together.
- **Callers.** inflate and deflate call `adler32`. Whether they meet its
  precondition is untested.
- **Size.** The longest function proven here is 65 lines. `inflate.c` is
  1443 lines, and its main function alone is about 680. We have no
  measurement of how VST behaves at that size.
- **A specification with choices.** Adler-32 has one right answer for
  each input. The inflate specification must say which streams are
  accepted and how output may be split across calls.

## Suggested improvements to Milestone 1

These are recommendations. They are ordered by how much we think each
matters before C proofs for inflate begin. Milestone 2 is the reference
model for inflate and has no C proof, so none of these blocks its start.

### Worth doing before continuing

1. **One statement about executions for `adler32.c`.** Write a small client
   program with a `main` that calls the five functions, apply VST's
   soundness theorem to it, and state what follows in CompCert's
   semantics. Everything we say about the code as shipped has to pass
   through this step, and we have never taken it. It is the piece of the
   method most likely to hold a surprise. Our guess is that it is a few
   days of work, most of it learning how VST states the theorem.
2. **Prove T0003.** It is the one unproven obligation the claim relies on,
   and its ledger entry calls it the simplest of the three and estimates a
   few hundred lines. Its premise is a statement about executions, so it
   needs item 1 to be of use. With both done, the claim for `adler32.c`
   would rest on no unproven obligation of ours.
3. **Let the traceability file point into the C proofs.** Two of the three
   pending sentences are already established by proofs it cannot name.
   This is small.
4. **Move the tick theorems out of the spike.** `TickStatements.v` and
   `TickBound.v` are cited as evidence for criterion 6 and still live in
   `spikes/transfer`. The cost proofs in `spikes/termination` are
   superseded by `proofs/adler32`. Promote the first and retire or mark
   the second, so that nothing the record cites is labelled exploratory.
5. **Have someone else read the specification.** The claim says no one
   outside the project has. The text to read is about 350 lines. It will
   never be shorter than it is now.

### Worth doing alongside Milestone 2

6. **Attempt the second tick theorem.** That erasing the ticks preserves
   behavior is stated and no proof has been tried, so the statement itself
   is untested. Bounded work is one of the four reasons the project
   exists, and today there is no termination theorem for any function,
   instrumented or not. With items 1 and 6 there would be one.
7. **Decide how to stop writing each proof twice.** The proof with ticks of
   `adler32_z` is 689 lines and repeats the 507 lines of the plain proof.
   The guarded proof repeats another. For inflate that would mean three
   proofs of a very large function. One option to weigh: once erasure is
   proven for ticks and for guards, prove only the instrumented and
   guarded form, and get everything about the original from the theorems.
   That makes T0002 and T0003 carry all the weight, which is a reason to
   prove them first. This is a design decision and should be recorded as
   one.
8. **Strengthen mutation testing a little.**
   - Record the time each mutant takes, so that a slow run can be
     explained. The spread between 24 and 50 minutes still is not.
   - Run the proofs with ticks against every mutant on their own, at least
     once. As run, they are reached only by the 4 survivors.
   - Give the build order a test, since it has already failed silently
     once.
   - Run the full check on a schedule in continuous integration, so that
     it is not skipped for days on an argument that it need not be run.
9. **Split the README.** It is 1667 lines, and the dated progress entries
   sit between the decisions and the open questions. A reader who wants
   the current state has to read the history. We suggest moving the dated
   entries to a log file and keeping in the README only what is true now.

### Not worth doing now

- **Closing the two zero-length calls.** They are limits of the tools, a
  caller can skip the call, and the same question will come back in
  inflate with more at stake. Better answered there.
- **The secondary tool for evaluation order.** It was out of scope, the
  file has almost nothing for it to find, and it is better set up once for
  several files.
- **Other configurations.** One cell of the matrix is the plan.

## Lessons to carry forward

1. **A specification we generate or derive needs a proof that it can be
   met.** Implication in one direction passes for a contract that nothing
   satisfies. For every derived contract, prove the converse or exhibit a
   call that meets it.
2. **Write the gate with the artifact.** The axiom check and the review
   of preconditions each found something the first time they were run. A
   check that lists
   every item and fails on a missing one beats one that samples. The
   checks do not judge reasons, and we should keep saying so.
3. **Word exit criteria by the theorem or the measurement.** Criterion 6
   was met "as worded" with one theorem unproven, because it allowed "a
   recorded status". Criterion 7 was "answered" in a toy. Neither was
   wrong, but closing on them left the milestone's main question partly
   open. For Milestone 2, each criterion should name what will exist and
   how it is checked, and separate "decided" from "demonstrated".
4. **Rerun the expensive checks at every boundary, and schedule them.**
   The argument for skipping the full mutation run was correct about the
   results and still hid a fault in the tool.
5. **A shortcut in a tool is code, and needs a test.** Anything that "only
   saves time" can stop saving it without failing.
6. **Do platform-independent work early, and count only the run on the
   target.** Pin nothing that names the target.
7. **Edge cases cost more than the main case.** The buffer of length zero
   took its own proof file, a change to the contracts, and two recorded
   limits. In inflate the same kind of case appears at every buffer
   boundary. Budget for it, and design the buffer description first.
8. **Expect findings, and expect them early.** The simplest file had one.
   The path from a failed proof to a ledger entry, a patch, and a witness
   worked and should be used unchanged.
9. **Prove narrow, then derive wide.** Prove each case against the code
   under the contract that suits the proof. Derive the contract a caller
   reads by subsumption, in both directions.
10. **Shared tactics belong in one place.** Local tactics with common names
    in several files will collide. Put them in `proofs/lib` or give them
    names that cannot.
11. **Keep the claim and its checked list of references together.** The
    claim took three sentences where the objective asked for one, so that
    the limits are in the part someone would quote. For inflate the list
    of limits will be longer. The same form should hold.
12. **Record a time only from a run that was not interrupted,** and take it
    from the tool, not from the wall.
13. **Small does not mean representative.** Roughly 4000 lines of proof
    for 164 lines of C, in three days, is a measurement of this file. It
    is not an estimate for inflate, for the reasons under "What the
    milestone did not exercise".

## One open question for the plan

Milestone 2 as written builds the reference model and fuzzes zlib against
it. It does not depend on anything left open here. The C proofs for
inflate do. We recommend that the plan for the next milestones say when
items 1, 2, 6, and 7 above are done, and that no C proof of an inflate
function starts before item 7 is decided.
