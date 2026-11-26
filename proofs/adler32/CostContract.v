(** * Adler-32: the contracts with a cost bound (Layer 3)

    Each contract of [Contract.v] and [Combine.v] in its form with ticks.
    The form with ticks is a contract for the function with a counter
    added, in [Ticked.v].  It says everything the plain contract says, and
    also that the call spends at most a stated number of ticks.

    One tick is spent on entry to a function and one at each test of a
    loop condition, including the last test, which fails.

    Each contract is given twice here.

    - Written out, such as [adler32_z_ticked_contract], so that it can be
      read, and used when proving a caller.
    - Generated, such as [adler32_z_generated], by [with_ticks] from the
      precondition and postcondition of the plain contract.  The tactic
      [ticked_form] takes those two out of the plain contract's own
      definition.

    [CostContractProof.v] proves that each written contract and its
    generated one say the same, and that each pair of a plain and a
    generated contract is [two_forms] of one precondition and one
    postcondition.

    This file holds definitions only. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.lib Require Import Ticks TickLogic.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Spec Contract
  Combine.

(** The counter is the one global variable of the functions with ticks. *)
Definition Vprog_ticks : varspecs := [(_fvz_ticks, tulong)].

(** ** The costs

    [adler32_z] with a null buffer returns at once, having spent the tick
    of its entry.  With a buffer of [len] bytes it spends at most one tick
    for each block of 5552 bytes, one for each 16 bytes, and 19 more. *)
Definition buffer_cost (len : Z) : Z := len / 5552 + len / 16 + 19.

Definition adler32_z_cost (b : buffer_arg) (len : Z) : Z :=
  match b with
  | Null => 1
  | Buffer _ _ _ _ => buffer_cost len
  end.

(** [adler32] spends one tick and calls [adler32_z]. *)
Definition adler32_cost (b : buffer_arg) (len : Z) : Z :=
  1 + adler32_z_cost b len.

(** The combine functions have no loop. *)
Definition combine_internal_cost : Z := 1.
Definition adler32_combine_cost : Z := 2.

(** ** Written out *)

Definition adler32_z_ticked_contract : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, b : buffer_arg, base : val, len : Z, gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned;
          0 <= len <= Int64.max_unsigned;
          buffer_ok b len;
          adler32_z_cost b len <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); buffer_ptr b base;
            Vlong (Int64.repr len))
    GLOBALS (gv)
    SEP (buffer_rep b base; ticks gv t)
  POST [ tulong ]
    EX r : Z, EX used : Z,
    PROP (adler32_spec adler (buffer_model b) r; 0 <= r < 4294967296;
          0 <= used <= adler32_z_cost b len)
    RETURN (Vlong (Int64.repr r))
    SEP (buffer_rep b base; ticks gv (t - used)).

Definition adler32_ticked_contract : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, b : buffer_arg, base : val, len : Z, gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned;
          0 <= len <= Int.max_unsigned;
          buffer_ok b len;
          adler32_cost b len <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); buffer_ptr b base;
            Vint (Int.repr len))
    GLOBALS (gv)
    SEP (buffer_rep b base; ticks gv t)
  POST [ tulong ]
    EX r : Z, EX used : Z,
    PROP (adler32_spec adler (buffer_model b) r; 0 <= r < 4294967296;
          0 <= used <= adler32_cost b len)
    RETURN (Vlong (Int64.repr r))
    SEP (buffer_rep b base; ticks gv (t - used)).

Definition combine_internal_ticked_spec : ident * funspec :=
 DECLARE _adler32_combine_
  WITH adler1 : Z, adler2 : Z, len2 : Z, gv : globals, t : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned; 0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed;
          combine_internal_cost <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (ticks gv t)
  POST [ tulong ]
    EX r : int64, EX used : Z,
    PROP (adler32_combine_spec adler1 adler2 len2 (Int64.unsigned r);
          0 <= used <= combine_internal_cost)
    RETURN (Vlong r)
    SEP (ticks gv (t - used)).

Definition adler32_combine_ticked_funspec : ident * funspec :=
 DECLARE _adler32_combine
  WITH adler1 : Z, adler2 : Z, len2 : Z, gv : globals, t : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned; 0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed;
          adler32_combine_cost <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (ticks gv t)
  POST [ tulong ]
    EX r : int64, EX used : Z,
    PROP (adler32_combine_spec adler1 adler2 len2 (Int64.unsigned r);
          0 <= used <= adler32_combine_cost)
    RETURN (Vlong r)
    SEP (ticks gv (t - used)).

Definition adler32_combine64_ticked_funspec : ident * funspec :=
 DECLARE _adler32_combine64
  WITH adler1 : Z, adler2 : Z, len2 : Z, gv : globals, t : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned; 0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed;
          adler32_combine_cost <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (ticks gv t)
  POST [ tulong ]
    EX r : int64, EX used : Z,
    PROP (adler32_combine_spec adler1 adler2 len2 (Int64.unsigned r);
          0 <= used <= adler32_combine_cost)
    RETURN (Vlong r)
    SEP (ticks gv (t - used)).

(** ** Generated

    [ticked_form c cost] is [with_ticks] applied to the precondition and
    postcondition found in the definition of the plain contract [c]. *)
Ltac ticked_form c cost :=
  let d := eval hnf in c in
  match d with
  | (_, NDmk_funspec ?sig ?cc ?A ?P ?Q) =>
      exact (with_ticks sig cc A cost P Q)
  end.

Definition adler32_z_generated : funspec :=
  ltac:(ticked_form adler32_z_contract
          (fun w : Z * buffer_arg * val * Z =>
             let '(_, b, _, len) := w in adler32_z_cost b len)).

Definition adler32_generated : funspec :=
  ltac:(ticked_form adler32_contract
          (fun w : Z * buffer_arg * val * Z =>
             let '(_, b, _, len) := w in adler32_cost b len)).

Definition combine_internal_generated : funspec :=
  ltac:(ticked_form combine_internal_spec
          (fun _ : Z * Z * Z => combine_internal_cost)).

Definition adler32_combine_generated : funspec :=
  ltac:(ticked_form adler32_combine_funspec
          (fun _ : Z * Z * Z => adler32_combine_cost)).

Definition adler32_combine64_generated : funspec :=
  ltac:(ticked_form adler32_combine64_funspec
          (fun _ : Z * Z * Z => adler32_combine_cost)).
