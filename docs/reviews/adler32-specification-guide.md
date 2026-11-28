# Guide to reviewing the Adler-32 specification

Written 2026-11-27, for a reader with a degree in mathematics and graduate
work in theoretical computer science. It assumes you can read a formal
definition and a logical formula. It does not assume you know Rocq, C's
finer rules, separation logic, or zlib.

## What the review is for

A proof checker confirms that a theorem follows from its definitions. It
cannot confirm that the definitions say what we meant. If
`spec/format/Adler32.v` defined some other checksum, every proof would
still pass, and would be about that other checksum.

So about 350 lines of this repository have to be read and believed by a
person. Nobody has read them but their author. This review is that
reading.

Two things about it should be said plainly.

- **You are not an outside reader.** You directed the work. That is far
  better than no reader, and it is not the independent review the claim
  says is missing. When you are done, limit 10 of
  [claims/adler32.md](../../claims/adler32.md) should say who read the
  specification and what came of it, and should still say that no zlib
  expert or verification expert has.
- **This guide was written by the author of the specification.** Where it
  points at risks, it points at the ones the author can see. The mistakes
  most worth finding are the ones not listed here. For that reason the
  guide asks you to form your own reading first, and puts its own
  questions last.

## What to read

Three parts, in order of importance. Part A is the review. Parts B and C
are worth doing if you have the time.

| Part | What | Size |
|---|---|---|
| A | The specification text | About 350 lines in five files |
| B | The records that a tool keeps in step but does not judge | Four files, read selectively |
| C | The statements of the theorems about executions | About 100 lines of statements |

### What not to read

- **Proof scripts.** Everything between `Proof.` and `Qed.` The checker
  reads those. If a statement is right and the proof is accepted, the
  proof's content does not matter to the claim.
- **`Adler32Facts.v` and `Adler32Tests.v`, as specification.** They are
  evidence, not definitions. They are very useful as an aid: see "Use the
  consequences" below.
- **The tools.** A bug in a check is a real risk, and a different review.

## Part A: the specification text

### The sources

Read these first, before any Rocq. They are short.

| Source | Where | What |
|---|---|---|
| RFC 1950, section 2.2, the ADLER32 field | `references/rfc1950.txt`, from line 318 | The definition in prose |
| RFC 1950, section 8.2 | from line 479 | Rationale, and two checkable facts |
| RFC 1950, section 9 | from line 511 | The sample code |
| The zlib manual | `upstream/zlib/zlib.h`, from line 1819 | `adler32`, `adler32_z`, `adler32_combine` |

### The files

| Order | File | Lines | What it must say |
|---|---|---|---|
| 1 | `spec/format/Bytes.v` | 17 | What a byte is |
| 2 | `spec/format/Adler32.v` | 91 | What RFC 1950 says Adler-32 is, twice: from the prose and from the sample code |
| 3 | `spec/api/Adler32.v` | 71 | What the manual promises each function returns |
| 4 | `proofs/adler32/Contract.v` | 124 | What a call to `adler32_z` or `adler32` needs and guarantees, in C terms |
| 5 | `proofs/adler32/Combine.v`, lines 66 to 81 and 215 to 243 | 45 | The same for the three combine functions |

### How to read: first pass

For each file, in this order:

1. **Read the source passage and write down what you would define.** A
   line or two per sentence is enough. Do this before you open the Rocq
   file. It is the only moment at which you have a reading that is not
   ours.
2. **Read the Rocq file and compare.** Every difference is worth a note,
   whether or not it turns out to matter.
3. **Compute something by hand, then by machine.** See "Try it" below.
4. **Ask of each definition what it allows that it should not, and what
   it forbids that it should not.** A specification can be wrong in
   either direction. Too weak is the more dangerous: a relation that
   allows any result is satisfied by every program.

Do not read the last section of this guide until you have done this for
all five files.

### Enough Rocq to read the definitions

- **`Definition name (x : T) : U := body.`** A function or a constant.
  `Fixpoint` is the same with structural recursion. `Inductive` introduces
  a data type by its constructors.
- **`Z`** is the mathematical integers, unbounded. `list Z` is a finite
  sequence. `[]` is empty, `x :: rest` puts `x` in front, `a ++ b` joins.
- **`mod` and `/` on `Z` are floor division.** The remainder takes the
  sign of the divisor: `(-7) mod 5` is 3 and `(-7) / 5` is -2. This
  differs from C, where the quotient is rounded toward zero. It matters
  wherever a definition is applied to a negative number.
- **`fold_left f l a`** applies `f` along the list from the left, starting
  from `a`: for `[x; y]` it is `f (f a x) y`. `fold_right f a l` goes from
  the right. `map f l` applies `f` to each element.
- **`Prop`** is the type of propositions. A definition of type `Prop` is
  a predicate or a relation. `A -> B` between propositions is implication,
  `/\` is and, `\/` is or, `forall` and `exists` are as usual.
- **`option T`** is either `None` or `Some x`. `match ... with` is case
  analysis.
- **`Forall P l`** says every element of `l` satisfies `P`.
- **`Z.of_nat (length l)`** is the length of a list, as an integer.

### Enough separation logic to read a contract

Files 4 and 5 are not plain mathematics. A contract has this shape:

```
DECLARE _adler32_z
 WITH adler : Z, b : buffer_arg, base : val, len : Z
 PRE [ tulong, tptr tuchar, tulong ]
   PROP (...) PARAMS (...) SEP (...)
 POST [ tulong ]
   EX r : Z, PROP (...) RETURN (...) SEP (...)
```

Read it as follows. Take any values for the variables after `WITH`.
Suppose the function is called with the arguments listed in `PARAMS`, the
facts in the first `PROP` hold, and the caller owns the memory described
in the first `SEP`. Then:

- the call does not go wrong in the semantics of C that the proofs use,
  which is CompCert's. For example, it does not read outside an object.
  This covers most of what the C standard leaves undefined, not all of
  it, and the claim lists what is left;
- if the call returns, there is an `r` for which the facts in the second
  `PROP` hold, the value returned is the one in `RETURN`, and the memory
  described before is now as the second `SEP` describes it;
- any other memory the caller owns is untouched. That is not written in
  the contract. It is a rule of the logic.

It says nothing about whether the call returns, or how long it takes.

The vocabulary:

- **`tulong`, `tuint`, `tlong`, `tptr tuchar`** are the C types `unsigned
  long`, `unsigned int`, `long`, and pointer to `unsigned char`. On this
  target `long` has 64 bits and `int` has 32.
- **`Vlong (Int64.repr z)`** is the 64-bit machine value that represents
  the integer `z`, taken modulo 2^64. With `0 <= z <= Int64.max_unsigned`
  in `PROP`, each machine value corresponds to exactly one `z`.
  `Vint (Int.repr z)` is the same at 32 bits.
- **`nullval`** is the null pointer. **`offset_val n p`** is the pointer
  `p` moved forward by `n` bytes.
- **`data_at sh t v p`** says that the memory at `p` holds the value `v`
  of C type `t`, and that the holder of this fact has the share `sh` of
  that memory. `tarray tuchar n` is an array of `n` bytes.
- **A share** is a degree of ownership. A full share allows writing. A
  readable share allows reading. Some shares allow neither but still show
  that the memory is allocated. `sepalg.nonidentity sh` says the share is
  not the empty one.
- **`list val`** is a list of machine values, which may include the value
  of uninitialized memory. `map Vubyte bs` is a list of initialized bytes.
- **`bytes_of bs`** turns machine bytes into the integers 0 to 255 that
  the mathematical layers use.

### Try it

After `tools/in-container.sh make`, put a file such as this in
`build/try/Try.v`. The `build` directory is not tracked.

```
From Stdlib Require Import ZArith List.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
Import ListNotations.
Local Open Scope Z_scope.

Compute adler32 [87; 105; 107; 105; 112; 101; 100; 105; 97].
Compute prefixes [1; 2; 3].
Compute (-7) mod 5.
```

and run

```bash
tools/in-container.sh rocq compile -Q spec/format fvzlib.format -Q spec/api fvzlib.api build/try/Try.v
```

The first line prints 300286872, which is `0x11e60398`, the Adler-32 of
"Wikipedia".

For a check that owes nothing to this project, compare with any zlib you
have:

```bash
python3 -c "import zlib; print(zlib.adler32(b'Wikipedia'))"
```

Work one small case entirely by hand, from the RFC's prose and not from
our definition. A two-byte input is enough. Then compute it.

### Use the consequences

`spec/format/Adler32Facts.v` and `spec/api/Adler32Facts.v` hold theorems
that follow from the definitions. Read their statements, not their
proofs. If a consequence surprises you, either you have learned something
or a definition is wrong.

The ones that bear most on whether the definitions are right:

| Theorem | File | Says |
|---|---|---|
| `update_1` | format | The reading from the sample code, started at 1, equals the reading from the prose |
| `s2_unreduced` | format | Reducing each term of the second sum or not gives the same result |
| `second_sum_abc` | format | The RFC's own example: for bytes a, b, c the second sum is 3a + 2b + c + 3 |
| `update_adler32` | format | Continuing a checksum over more bytes gives the checksum of the whole |
| `adler32_reference_meets_spec` | api | The specification of `adler32` can be met |
| `adler32_spec_deterministic` | api | When the argument is a checksum, the specification fixes the result |
| `checksum_form_iff` | api | Exactly which integers are the checksum of something |
| `usage_example` | api | The manual's usage loop computes the checksum of all the data |
| `combine_reference_meets_spec` | api | The specification of `adler32_combine` can be met |
| `adler32_combine_spec_negative` | api | With a negative length the specification allows any result |

`spec/format/Adler32Tests.v` holds test vectors. Its header says where
the expected values come from: they were computed from the RFC's sample
code, and the build checks each against the pinned zlib. Check one or two
against a source of your own.

## Part B: records a tool keeps in step but does not judge

Each of these has a check that fails the build if the record falls out of
step with the code. None of the checks reads the reasons. The reasons are
prose, and only a person can find one unconvincing.

| File | Read | Ask |
|---|---|---|
| `trace/adler32.toml` | The 9 entries with `status = "not-covered"`, the 1 pending, and the notes on the 2 that name a C proof | Is each sentence of the sources mapped to the right thing? Is each reason for not covering a sentence a good one? |
| `audit/preconditions-adler32.toml` | The 11 clauses with verdict `needed`, `promise` or `limit` | Is each demand on the caller really needed? Could a real caller know it has met it? |
| `audit/mutants-adler32.toml` | All 4 entries | Is each surviving mutant harmless for the reason given? |
| `env/build-check-allow.toml` | Both entries. They accept the same difference, once for each system the build check has run on. The Linux one is the one that counts. | Is the accepted difference between the built and the verified source harmless? |

Then read the three sentences of the claim in
[claims/adler32.md](../../claims/adler32.md) once more, with the
specification fresh in mind. Ask whether a maintainer who read only those
three sentences would come away believing something that is not proven.

## Part C: statements of the theorems about executions

These are not in the 350 lines, and the claim's three sentences do not
depend on your reading them. But they are statements someone has to
believe mean what the prose says.

| Statement | File | Lines to read |
|---|---|---|
| `never_goes_wrong`, `reachable` | `proofs/lib/Executions.v` | The two definitions |
| `more_permission_same_call`, `inline_calls_deterministic` | `proofs/lib/Soundness.v` | The two definitions. They are hypotheses of everything below. |
| `plain`, `returns`, and the statement of `verified_program_never_goes_wrong` | `proofs/lib/Soundness.v` | The conditions on `main`, and the theorem. It is stated inside a section, so its hypotheses are the lines that begin `Hypothesis` in the section named `JOIN`. |
| `tests`, `no_violation`, and the statement of `guards_removed` | `proofs/lib/GuardSound.v` | Near the end of the file |
| The program | `proofs/adler32_client/client.c` | All 40 lines |
| `client_never_goes_wrong` | `proofs/adler32_client/Client.v` | The statement |
| `remainder`, `remainder_operand_not_negative` | `proofs/adler32_client/Guarded.v` | The definition and the statement |

The question for each is the same as in Part A: does the formal statement
say what the README beside it says in words?

`never_goes_wrong` uses CompCert's notions of a program's behaviors. To
judge it you would need CompCert's definitions of `program_behaves` and
`not_wrong`, which are not in this repository. It is reasonable to stop
at noting that.

## How to record what you find

Write findings into `docs/reviews/adler32-specification-review.md`. One
entry per finding:

- **Where.** File and line, or the name of the definition.
- **What the source says.** Quoted.
- **What the text says.**
- **Why it matters,** or why you think it may not.
- **Kind.** One of the five below.

| Kind | Meaning |
|---|---|
| Wrong | The definition says something the source does not |
| Weak | The definition allows something the source rules out |
| Strong | The definition or precondition demands something the source does not |
| Silent choice | The source is ambiguous and the text picks a reading without saying so |
| Unclear | You could not tell what the text says, or the comment and the definition disagree |

Record the places you checked and found right, too, in a line each. A
review that lists only problems cannot be told apart from one that looked
at little.

A finding of the first three kinds changes the specification, and then
the proofs have to be made to pass again. That is the review working. A
"silent choice" becomes a stated one, with a theorem that the choice does
not matter if there is one to be had.

If you find the guide itself wrong or misleading, that is a finding.

## How long

A guess, not a measurement: half a day for Part A, two or three hours for
Part B, an hour or two for Part C.

## Second pass: the author's questions

Read this only after your own first pass over all five files. These are
the places where the author made a choice, or where a mistake would be
easy to make and hard for a proof to catch.

### `spec/format/Adler32.v`

1. **Which s1 values does s2 add?** "s2 is the sum of all s1 values." We
   take one value for each byte consumed, and do not count the initial 1.
   So `s2 [] = 0` and `s2 [a] = (1 + a) mod 65521`. `prefixes` is how
   that is expressed. Is this the reading the RFC intends? The sample
   code agrees with it, and `update_1` proves the agreement.
2. **"Both sums are done modulo 65521."** Reduced at each step, or once at
   the end? `s2_unreduced` shows it makes no difference to s2. Is there
   any other place where the order of reduction could matter?
3. **Are the two readings independent?** They were written by one author
   on one day. What could both have wrong? Candidates: the constant
   65521, the order in `s2 * 65536 + s1`, and what counts as a byte. The
   test vectors and the comparison with a real zlib are the evidence
   against a shared mistake.
4. **Definitions are total over all integers.** `adler32` accepts a list
   containing -3 or 1000. Nothing is claimed about such lists, but check
   that no statement you care about silently includes them.
5. **`low16` and `high16` on a negative or a large argument.** They stand
   for `adler & 0xffff` and `(adler >> 16) & 0xffff`. In C the argument
   is unsigned and may exceed 32 bits on this target. Do the definitions
   agree with the C expressions for every non-negative integer?
6. **What is deliberately absent.** The byte order in which the checksum
   is stored in a stream, and "excluding any dictionary data". Both
   belong to the stream format. Is anything else absent that should not
   be?

### `spec/api/Adler32.v`

7. **Is the conditional form right?** `adler32_spec` promises a result
   only when the `adler` argument is the checksum of some earlier data.
   For any other argument it allows any result. The manual says "update a
   running Adler-32 checksum". Is it right to read that as a
   precondition on the argument? This is the weakest point of the
   specification by design, so it deserves the hardest look.
8. **Quantifying over every `earlier`.** Many byte sequences share a
   checksum. The relation requires the result to be right for all of them
   at once. Convince yourself this is consistent and is what is wanted.
9. **The null buffer.** The relation ignores both `adler` and the length
   when the buffer is null. The manual: "If buf is Z_NULL, this function
   returns the required initial value for the checksum." Does the manual
   mean this for every length?
10. **Where is the 32-bit range?** "An Adler-32 value is in the range of a
    32-bit unsigned integer." It is not in the relation. For `adler32` it
    is in the contract, unconditionally. For the combine functions it is
    promised only when the arguments are checksums. Is that split
    faithful to the manual?
11. **`adler32_combine_spec`.** The length of the first sequence does not
    appear, as the manual says it need not. A negative `len2` allows any
    result. So does a `len2` that is not the length of any sequence with
    checksum `adler2`. Is each of these what the manual means?
12. **`running_checksum` requires `all_bytes`.** Is there a use of it
    where that side condition makes a statement vacuous?

### `proofs/adler32/Contract.v` and the contracts in `Combine.v`

13. **The buffer.** A caller passes either a null pointer or a run of
    bytes inside an array it owns, with anything before and after the
    run. Is that every call the manual allows? Two kinds of call with a
    length of zero are known to be left out, and the file says which.
14. **Memory unchanged.** The same `buffer_rep` appears before and after.
    Check that nothing in the postcondition could let the function have
    changed the bytes.
15. **From memory to mathematics.** The bytes in memory are
    `map Vubyte bs`, and the specification is applied to `bytes_of bs`.
    Check that these are the same bytes.
16. **Any 64-bit `adler`.** The contract admits every value of the type,
    including ones above 2^32. For those the Layer 2 relation promises
    nothing about the value. Is that what a caller would expect?
17. **The two lengths.** `adler32` takes a 32-bit length and `adler32_z` a
    64-bit one. Check that each contract bounds `len` by its own type.
18. **The combine contracts.** They own no memory. The result is a 64-bit
    value whose unsigned reading satisfies the relation. `len2` is signed.
19. **What a contract cannot say.** Nothing about termination, time, or
    other threads. Is anything the manual promises thereby left out?
