(** * Spike: cost contracts for the Adler-32 combine functions

    The three combine functions of patched zlib 1.4, with ticks added.
    None has a loop, so each costs a fixed number of ticks: one for each
    function entered.

    - The internal function [adler32_combine_] costs at most 1.
    - [adler32_combine] and [adler32_combine64] each enter themselves and
      the internal function, and cost at most 2.

    As in the rest of this spike, the contracts are about cost and memory
    safety only.  They say nothing about the value returned.  The
    functional proof is in [proofs/adler32/Combine.v], for the code without
    ticks. *)

Require Import VST.floyd.proofauto.
From fvzlib.proofs.lib Require Import Ticks.
Require Import adler32 adler32_ticked Buffer verif_adler32_z_cost.

Definition combine_internal_cost : Z := 1.
Definition adler32_combine_cost : Z := 2.

Definition combine_internal_cost_spec : ident * funspec :=
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
    PROP (0 <= used <= combine_internal_cost)
    RETURN (Vlong r)
    SEP (ticks gv (t - used)).

Definition adler32_combine_cost_spec : ident * funspec :=
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
    PROP (0 <= used <= adler32_combine_cost)
    RETURN (Vlong r)
    SEP (ticks gv (t - used)).

Definition adler32_combine64_cost_spec : ident * funspec :=
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
    PROP (0 <= used <= adler32_combine_cost)
    RETURN (Vlong r)
    SEP (ticks gv (t - used)).

(* Forget what the two sums are.  This proof makes no claim about them. *)
Ltac forget_combine_sums :=
  match goal with |- context [temp _sum1 (Vlong ?a)] =>
    let x := fresh "s1" in set (x := a); clearbody x end;
  match goal with |- context [temp _sum2 (Vlong ?a)] =>
    let x := fresh "s2" in set (x := a); clearbody x end.

Lemma body_combine_internal_cost :
  semax_body Vprog_ticks [combine_internal_cost_spec]
             f_adler32_combine__ticked combine_internal_cost_spec.
Proof.
  start_function. unfold ticks, combine_internal_cost in *.
  spend_tick.
  forward_if
    (PROP (0 <= len2)
     LOCAL (temp _adler1 (Vlong (Int64.repr adler1));
            temp _adler2 (Vlong (Int64.repr adler2));
            temp _len2 (Vlong (Int64.repr len2)); gvars gv)
     SEP (data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { rewrite !Int64.signed_repr in * by rep_lia. return_using 1. }
  { rewrite !Int64.signed_repr in * by rep_lia. forward. entailer!. }
  Intros.
  (* len2 %= BASE.  The divisor is 65521, so this signed remainder is not
     the one case that overflows. *)
  forward.
  { entailer!.
    match goal with
    | H : _ /\ Int.repr 65521 = Int.mone |- _ =>
        destruct H as [_ H]; apply (f_equal Int.unsigned) in H;
        rewrite Int.unsigned_repr, Int.unsigned_mone in H by rep_lia; rep_lia
    end. }
  forward. forward. forward. forward. forward. forward.
  forget_combine_sums.
  (* if (sum1 >= BASE) sum1 -= BASE;  twice *)
  forward_if
    (EX v : int64,
     PROP ()
     LOCAL (temp _sum1 (Vlong v); temp _sum2 (Vlong s2); gvars gv)
     SEP (data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { forward. witness_of _sum1. entailer!. }
  { forward. witness_of _sum1. entailer!. }
  Intros a.
  forward_if
    (EX v : int64,
     PROP ()
     LOCAL (temp _sum1 (Vlong v); temp _sum2 (Vlong s2); gvars gv)
     SEP (data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { forward. witness_of _sum1. entailer!. }
  { forward. witness_of _sum1. entailer!. }
  Intros b.
  (* if (sum2 >= 2 * BASE) sum2 -= 2 * BASE;  if (sum2 >= BASE) sum2 -= BASE; *)
  forward_if
    (EX v : int64,
     PROP ()
     LOCAL (temp _sum1 (Vlong b); temp _sum2 (Vlong v); gvars gv)
     SEP (data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { forward. witness_of _sum2. entailer!. }
  { forward. witness_of _sum2. entailer!. }
  Intros c.
  forward_if
    (EX v : int64,
     PROP ()
     LOCAL (temp _sum1 (Vlong b); temp _sum2 (Vlong v); gvars gv)
     SEP (data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { forward. witness_of _sum2. entailer!. }
  { forward. witness_of _sum2. entailer!. }
  Intros d.
  return_using 1.
Qed.

Definition Gprog_combine : funspecs :=
  [combine_internal_cost_spec; adler32_combine_cost_spec;
   adler32_combine64_cost_spec].

(* Both public functions do the same: spend a tick, call the internal
   function, and return what it returned. *)
Ltac call_internal adler1 adler2 len2 gv t :=
  unfold adler32_combine_cost, combine_internal_cost in *;
  unfold ticks;
  spend_tick;
  forward_call (adler1, adler2, len2, gv, t - 1);
  [ unfold ticks; rewrite sub64_repr; cancel | ];
  let vret := fresh "vret" in
  let r := fresh "r" in
  let used := fresh "used" in
  Intros vret; destruct vret as [r used]; cbn [fst snd] in *;
  unfold combine_internal_cost in *;
  forward;
  Exists r (used + 1); unfold ticks; entailer!;
  apply derives_refl'; do 3 f_equal; lia.

Lemma body_adler32_combine_cost :
  semax_body Vprog_ticks Gprog_combine f_adler32_combine_ticked
             adler32_combine_cost_spec.
Proof. start_function. call_internal adler1 adler2 len2 gv t. Qed.

Lemma body_adler32_combine64_cost :
  semax_body Vprog_ticks Gprog_combine f_adler32_combine64_ticked
             adler32_combine64_cost_spec.
Proof. start_function. call_internal adler1 adler2 len2 gv t. Qed.
