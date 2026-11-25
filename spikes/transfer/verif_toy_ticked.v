(** * Spike: a VST cost contract for the instrumented toy function

    The contract adds a cost clause to the one in [verif_toy_nogoto.v].  The
    caller supplies a counter of at least [n0 + 2] ticks, and the function
    returns the counter less the ticks it used, which are at most
    [n0 + 2]: one on entry and one at the start of each loop iteration. *)

Require Import VST.floyd.proofauto.
Require Import toy toy_nogoto Ticks toy_ticked.
Require Import verif_toy_nogoto.

(** The counter is a global, so it has to be in the variable specifications. *)
Definition Vprog_ticks : varspecs := [(_fvz_ticks, tulong)].

(** The tick resource: the counter holds [t]. *)
Definition ticks (gv : globals) (t : Z) : mpred :=
  data_at Ews tulong (Vlong (Int64.repr t)) (gv _fvz_ticks).

Definition count_down_cost (n0 : Z) : Z := n0 + 2.

Definition count_down_ticked_spec : ident * funspec :=
 DECLARE _count_down
  WITH n0 : Z, stop : Z, out : val, sh : share, gv : globals, t : Z
  PRE [ tuint, tuint, tptr tuint ]
    PROP (0 <= n0 <= Int.max_unsigned; 0 <= stop <= Int.max_unsigned;
          writable_share sh;
          count_down_cost n0 <= t <= Int64.max_unsigned)
    PARAMS (Vint (Int.repr n0); Vint (Int.repr stop); out) GLOBALS (gv)
    SEP (data_at_ sh tuint out; ticks gv t)
  POST [ tuint ]
    EX used : Z,
    PROP (0 <= used <= count_down_cost n0)
    RETURN (Vint (Int.repr (stop_at n0 stop)))
    SEP (data_at sh tuint (Vint (Int.repr (n0 - stop_at n0 stop))) out;
         ticks gv (t - used)).

Definition Gprog_ticks : funspecs := [count_down_ticked_spec].

(** Step through one tick when the counter is known to be positive.  The
    branch that jumps to the missing label is closed by contradiction: it
    is reached only if the counter is zero. *)
(** Step through one tick when the counter is known to be positive.  The
    branch that jumps to the missing label is closed by contradiction: it
    is reached only if the counter is zero. *)
Ltac spend_tick :=
  forward;
  forward_if True;
  [ exfalso;
    match goal with
    | H : Int64.repr _ = Int64.zero |- _ =>
        change Int64.zero with (Int64.repr 0) in H;
        apply repr_inj_unsigned64 in H; rep_lia
    end
  | forward; entailer!
  | forward ].

(* Close what [entailer!] leaves: equalities between integer values, and
   entailments between two copies of a cell holding equal integers. *)
Ltac fin :=
  try solve [do 2 f_equal; lia];
  try solve [apply derives_refl'; do 3 f_equal; lia];
  try solve [cancel].

Lemma body_count_down_ticked :
  semax_body Vprog_ticks Gprog_ticks f_count_down_ticked count_down_ticked_spec.
Proof.
  start_function. unfold ticks, count_down_cost in *.
  spend_tick.                       (* the tick on entry *)
  forward.
  forward_loop
    (EX k : Z,
       PROP (0 <= k <= n0; stop <= k \/ n0 < stop)
       LOCAL (temp _n (Vint (Int.repr k));
              temp _steps (Vint (Int.repr (n0 - k)));
              temp _stop (Vint (Int.repr stop)); temp _out out; gvars gv)
       SEP (data_at_ sh tuint out;
            data_at Ews tulong (Vlong (Int64.repr (t - 1 - (n0 - k))))
                    (gv _fvz_ticks)))
    break:
    (PROP (stop <= 0 \/ n0 < stop)
     LOCAL (temp _n (Vint (Int.repr 0));
            temp _steps (Vint (Int.repr n0)); temp _out out; gvars gv)
     SEP (data_at_ sh tuint out;
          data_at Ews tulong (Vlong (Int64.repr (t - 2 - n0)))
                  (gv _fvz_ticks))).
  - Exists n0. entailer!; fin.
  - Intros k.
    spend_tick.                     (* the tick for this iteration *)
    forward_if (PROP (k <> 0)
       LOCAL (temp _n (Vint (Int.repr k));
              temp _steps (Vint (Int.repr (n0 - k)));
              temp _stop (Vint (Int.repr stop)); temp _out out; gvars gv)
       SEP (data_at_ sh tuint out;
            data_at Ews tulong (Vlong (Int64.repr (t - 2 - (n0 - k))))
                    (gv _fvz_ticks))).
    + forward; try entailer!; fin.
    + forward; try entailer!; fin.
    + Intros.
      forward_if (PROP (k <> stop)
         LOCAL (temp _n (Vint (Int.repr k));
                temp _steps (Vint (Int.repr (n0 - k)));
                temp _stop (Vint (Int.repr stop)); temp _out out; gvars gv)
         SEP (data_at_ sh tuint out;
              data_at Ews tulong (Vlong (Int64.repr (t - 2 - (n0 - k))))
                      (gv _fvz_ticks))).
      * (* where the goto was: the copied cleanup code *)
        forward. forward.
        (* VST has replaced k by stop here, since they are equal. *)
        Exists (n0 - stop + 2).
        rewrite stop_at_hit by lia. entailer!; fin.
      * forward; try entailer!; fin.
      * Intros. forward. forward.
        Exists (k - 1). entailer!; fin.
  - forward. forward.
    Exists (n0 + 2).
    rewrite stop_at_miss by lia. rewrite Z.sub_0_r. entailer!; fin.
Qed.
