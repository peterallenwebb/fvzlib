# Layer 3 design: contracts for the Adler-32 functions

Status: design adopted on 2026-11-24. Built in part on 2026-11-25, on the
x86-64 Linux target. The buffer argument was changed on 2026-11-26 by the
review of preconditions: see "The buffer argument" below.

- **Built and proven:** the contracts of `adler32_z` and `adler32` in the
  form without ticks, with the buffer argument described below. They are in
  `proofs/adler32/Contract.v`, under the names `adler32_z_contract` and
  `adler32_contract`, and proven in `ContractProof.v`.
- **Proven in the termination spike:** the cost bounds in the table below,
  for instrumented code.
- **Not built:** the form with ticks of each contract, and the generation
  of both forms from one definition. The draft at the end of this note is
  that form with ticks. It is kept as written on 2026-11-24, and nothing
  has been proven against it.

The decision itself is recorded in the README under "Layer 3 contracts".

## What each contract says

- **Arguments are unconstrained in value.** The checksum argument may be any
  64-bit value, and the length any value of its C type.
- **The result satisfies the Layer 2 specification.** Where the manual makes
  no promise, the contract makes none about the value.
- **Memory is untouched.** The buffer comes back as given, under the same
  share, so read-only buffers are allowed.
- **Cost is an upper bound.** The caller supplies a tick counter at least as
  large as the bound and gets back the counter less an amount no larger than
  the bound.
- **Bytes need no side condition.** The buffer holds machine bytes, whose
  integer values are bytes by construction.

## The buffer argument

A non-null buffer is described as a run of bytes inside an array that the
caller owns, with what the array holds before and after the run named. The
array as a whole must be non-empty. That makes the pointer valid even when
the run is empty, which the code needs, because it compares the pointer with
null and C defines that comparison only for a pointer that is null or points
into, or one past, a live object.

As adopted, the design asked that the whole array be readable and hold
initialized bytes. The review of preconditions on 2026-11-26 found that
nothing needs either outside the run, and the contracts as built ask less:

- **Only the run holds bytes.** What is before and after it is a list of
  values, which may be uninitialized.
- **Only a run that is not empty must be readable.** For an empty run the
  caller needs some part in the ownership of the array and no more.

The draft at the end of this note still has the form as adopted. The form
as built is in `proofs/adler32/Contract.v`, and the review is in
`audit/preconditions-adler32.toml`.

An earlier draft let the caller pass an arbitrary separation-logic predicate
as evidence of pointer validity. VST's ordinary contract form rejects a
predicate-valued parameter, with a universe inconsistency. The run-in-an-array
form avoids that.

A simpler corollary contract for a plain non-empty buffer, with nothing
before or after, is derived from the general one in `ContractProof.v`.

## Cost bounds

One tick is charged at each function entry and at each test of a loop
condition, including the final test that fails.

| Function | Bound in ticks | Status |
|---|---|---|
| `adler32_z` | len/5552 + len/16 + 19 | Proven for the instrumented code in the termination spike, for a non-null, non-empty buffer |
| `adler32` | one more than `adler32_z` | Proven in the same spike |
| `adler32_combine`, `adler32_combine64` | 2 | Proven for the instrumented code in the termination spike, for any arguments |

An earlier version of this note proposed `1 + len/5552 + len/16 + 15` for
`adler32_z`. That was three ticks too low, because it did not count the
final failing test of each loop. The draft contracts below still carry the
old formula and are to be updated when they are built.

## Two forms from one definition

Each contract is to exist in two forms generated from one definition. The
form with ticks is what VST proves about the instrumented code. The form
without ticks is what a downstream verifier imports for the real code. The
draft below shows only the form with ticks, and uses a placeholder for the
tick counter.

## Observations made while drafting

- **The checksum type is 64 bits wide on the first target.** "Fits in 32
  bits" is therefore a claim to prove, not a consequence of the type.
- **The combine functions can return more than 32 bits for invalid
  arguments.** On the development machine,
  `adler32_combine(0xFFFFFFF0, 0xFFFF0000, 1)` returned `0x1000bffef`.
  Neither argument is a valid Adler-32 checksum, and the manual promises
  nothing for such arguments, so this is not a defect. The contracts promise
  the 32-bit range unconditionally for `adler32` and `adler32_z`, and only
  through the Layer 2 specification for the combine functions.
- **A stronger, exact contract would need a precondition.** The one-byte path
  of `adler32_z` reduces with a single conditional subtraction, which is
  exact only when the incoming checksum halves are already reduced.

## Draft contracts

`ticks` stands in for the counter that instrumentation will add.
`adler32_spec` and `adler32_combine_spec` are the Layer 2 specifications.
The names ending in a prime avoid a clash with them in this draft.

```coq
Parameter ticks : globals -> Z -> mpred.

Definition bytes_of (bs : list byte) : list Z := map Byte.unsigned bs.

Lemma bytes_of_all_bytes bs : all_bytes (bytes_of bs).
Proof.
  unfold all_bytes, bytes_of. induction bs as [|b bs IH]; constructor; auto.
  unfold is_byte. pose proof (Byte.unsigned_range b) as H.
  change Byte.modulus with 256 in H. lia.
Qed.

(* What the caller passes as the buffer argument.  A non-null buffer is a
   run of bytes inside a readable array the caller owns: [before] precedes
   it and [after] follows it.  The array as a whole must be non-empty, which
   makes the pointer a valid one even when the run itself is empty. *)
Inductive buffer_arg :=
| Null
| Buffer (sh : share) (before bs after : list byte).

Definition buffer_model (b : buffer_arg) : option (list Z) :=
  match b with Null => None | Buffer _ _ bs _ => Some (bytes_of bs) end.

Definition buffer_ptr (b : buffer_arg) (base : val) : val :=
  match b with
  | Null => nullval
  | Buffer _ before _ _ => offset_val (Zlength before) base
  end.

Definition buffer_ok (b : buffer_arg) (len : Z) : Prop :=
  match b with
  | Null => True
  | Buffer sh before bs after =>
      readable_share sh /\ Zlength bs = len /\
      0 < Zlength (before ++ bs ++ after)
  end.

Definition buffer_rep (b : buffer_arg) (base : val) : mpred :=
  match b with
  | Null => emp
  | Buffer sh before bs after =>
      data_at sh (tarray tuchar (Zlength (before ++ bs ++ after)))
              (map Vubyte (before ++ bs ++ after)) base
  end.

Definition adler32_z_cost (len : Z) : Z := 1 + len / 5552 + len / 16 + 15.
Definition adler32_cost (len : Z) : Z := 1 + adler32_z_cost len.

Definition adler32_z_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, b : buffer_arg, base : val, len : Z, gv : globals, n : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned;
          0 <= len <= Int64.max_unsigned;
          buffer_ok b len;
          adler32_z_cost len <= n)
    PARAMS (Vlong (Int64.repr adler); buffer_ptr b base; Vlong (Int64.repr len)) GLOBALS (gv)
    SEP (buffer_rep b base; ticks gv n)
  POST [ tulong ]
    EX result : Z, EX used : Z,
    PROP (adler32_spec adler (buffer_model b) result;
          0 <= result < 4294967296;
          0 <= used <= adler32_z_cost len)
    RETURN (Vlong (Int64.repr result))
    SEP (buffer_rep b base; ticks gv (n - used)).

Definition adler32_spec' : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, b : buffer_arg, base : val, len : Z, gv : globals, n : Z
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned;
          0 <= len <= Int.max_unsigned;
          buffer_ok b len;
          adler32_cost len <= n)
    PARAMS (Vlong (Int64.repr adler); buffer_ptr b base; Vint (Int.repr len)) GLOBALS (gv)
    SEP (buffer_rep b base; ticks gv n)
  POST [ tulong ]
    EX result : Z, EX used : Z,
    PROP (adler32_spec adler (buffer_model b) result;
          0 <= result < 4294967296;
          0 <= used <= adler32_cost len)
    RETURN (Vlong (Int64.repr result))
    SEP (buffer_rep b base; ticks gv (n - used)).

Definition adler32_combine_spec' : ident * funspec :=
 DECLARE _adler32_combine
  WITH adler1 : Z, adler2 : Z, len2 : Z, gv : globals, n : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned;
          0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed;
          2 <= n)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2)) GLOBALS (gv)
    SEP (ticks gv n)
  POST [ tulong ]
    EX result : Z, EX used : Z,
    PROP (adler32_combine_spec adler1 adler2 len2 result;
          0 <= result <= Int64.max_unsigned;
          0 <= used <= 2)
    RETURN (Vlong (Int64.repr result))
    SEP (ticks gv (n - used)).
```
