(** * Spike: a VST contract for the toy function with its goto removed

    The original [f_count_down] contains a reachable goto, so VST can prove
    no contract for it.  This file proves an ordinary contract for the
    transformed function [f_count_down_nogoto]. *)

Require Import VST.floyd.proofauto.
Require Import toy toy_nogoto.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The value at which the count stops: [stop] if the count meets it on
    the way down from [n0], and 0 otherwise. *)
Definition stop_at (n0 stop : Z) : Z :=
  if zlt 0 stop then (if zle stop n0 then stop else 0) else 0.

Definition count_down_spec : ident * funspec :=
 DECLARE _count_down
  WITH n0 : Z, stop : Z, out : val, sh : share
  PRE [ tuint, tuint, tptr tuint ]
    PROP (0 <= n0 <= Int.max_unsigned; 0 <= stop <= Int.max_unsigned;
          writable_share sh)
    PARAMS (Vint (Int.repr n0); Vint (Int.repr stop); out)
    SEP (data_at_ sh tuint out)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (stop_at n0 stop)))
    SEP (data_at sh tuint (Vint (Int.repr (n0 - stop_at n0 stop))) out).

Definition Gprog : funspecs := [count_down_spec].

Lemma stop_at_hit n0 stop : 0 < stop <= n0 -> stop_at n0 stop = stop.
Proof. intros. unfold stop_at. destruct (zlt 0 stop), (zle stop n0); lia. Qed.

Lemma stop_at_miss n0 stop : stop <= 0 \/ n0 < stop -> stop_at n0 stop = 0.
Proof. intros. unfold stop_at. destruct (zlt 0 stop), (zle stop n0); lia. Qed.

(* Close the arithmetic goals that [entailer!] leaves about integer values. *)
Ltac arith := try solve [do 2 f_equal; lia].

Lemma body_count_down_nogoto :
  semax_body Vprog Gprog f_count_down_nogoto count_down_spec.
Proof.
  start_function.
  forward.
  forward_loop
    (EX k : Z,
       PROP (0 <= k <= n0; stop <= k \/ n0 < stop)
       LOCAL (temp _n (Vint (Int.repr k));
              temp _steps (Vint (Int.repr (n0 - k)));
              temp _stop (Vint (Int.repr stop)); temp _out out)
       SEP (data_at_ sh tuint out))
    break:
    (PROP (stop <= 0 \/ n0 < stop)
     LOCAL (temp _n (Vint (Int.repr 0));
            temp _steps (Vint (Int.repr n0)); temp _out out)
     SEP (data_at_ sh tuint out)).
  - (* the invariant holds on entry *)
    Exists n0. entailer!; arith.
  - (* the loop body *)
    Intros k.
    forward_if (PROP (k <> 0)
       LOCAL (temp _n (Vint (Int.repr k));
              temp _steps (Vint (Int.repr (n0 - k)));
              temp _stop (Vint (Int.repr stop)); temp _out out)
       SEP (data_at_ sh tuint out)).
    + forward; try entailer!.
    + (* n == 0: leave the loop *)
      forward; try entailer!; arith.
    + Intros.
      forward_if (PROP (k <> stop)
         LOCAL (temp _n (Vint (Int.repr k));
                temp _steps (Vint (Int.repr (n0 - k)));
                temp _stop (Vint (Int.repr stop)); temp _out out)
         SEP (data_at_ sh tuint out)).
      * (* n == stop: this is where the goto was.  The copied cleanup
           code stores the step count and returns. *)
        forward. forward.
        rewrite stop_at_hit by lia. entailer!; arith.
      * forward; try entailer!.
      * Intros. forward. forward.
        Exists (k - 1). entailer!; arith.
  - (* after the loop: the original cleanup code *)
    forward. forward.
    rewrite stop_at_miss by lia. rewrite Z.sub_0_r. entailer!; arith.
Qed.

Print Assumptions body_count_down_nogoto.
