(** * Spike: cost contracts for callers of adler32_z

    Two callers are proven here against the cost contract of [adler32_z].

    - The real [adler32] of patched zlib 1.4, with ticks added.  Its budget
      covers its own tick and the callee's.
    - A small client that calls [adler32_z] twice and refills the counter
      before each call.  The client needs no budget from its own caller. *)

Require Import VST.floyd.proofauto.
Require Import adler32 Ticks adler32_ticked Buffer verif_adler32_z_cost.

Definition adler32_cost (len : Z) : Z := adler32_z_cost len + 1.

Definition adler32_cost_spec : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, sh : share, bs : list byte, base : val, gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength bs <= Int.max_unsigned;
          adler32_cost (Zlength bs) <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); base; Vint (Int.repr (Zlength bs)))
    GLOBALS (gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
         ticks gv t)
  POST [ tulong ]
    EX r : int64, EX used : Z,
    PROP (0 <= used <= adler32_cost (Zlength bs))
    RETURN (Vlong r)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
         ticks gv (t - used)).

Definition Gprog_callers : funspecs := [adler32_z_cost_spec; adler32_cost_spec].

Lemma body_adler32_cost :
  semax_body Vprog_ticks Gprog_callers f_adler32_ticked adler32_cost_spec.
Proof.
  start_function. unfold adler32_cost in *.
  unfold ticks. assert (Hc : 0 <= adler32_z_cost (Zlength bs)).
  { unfold adler32_z_cost.
    pose proof (Z.div_pos (Zlength bs) 5552 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (Zlength bs) 16 ltac:(lia) ltac:(lia)). lia. }
  spend_tick.
  forward_call (adler, sh, bs, base, gv, t - 1).
  { unfold ticks. rewrite sub64_repr. cancel. }
  Intros vret. destruct vret as [r used]. cbn [fst snd] in *.
  forward.
  Exists r (used + 1). unfold ticks. entailer!.
  apply derives_refl'. do 3 f_equal. lia.
Qed.

(** ** A client that refills the counter before each call

<<
    unsigned long twice(const unsigned char *buf, unsigned long len) {
        unsigned long a;
        fvz_ticks = len / 5552 + len / 16 + 19;
        a = adler32_z(1, buf, len);
        fvz_ticks = len / 5552 + len / 16 + 19;
        a = adler32_z(a, buf, len);
        return a;
    }
>>

    The function is written here as a Clight syntax tree, with the
    identifiers of the Adler-32 file. *)

Definition budget : expr :=
  Ebinop Oadd
    (Ebinop Oadd
       (Ebinop Odiv (Etempvar _len tulong) (Econst_long (Int64.repr 5552) tulong) tulong)
       (Ebinop Odiv (Etempvar _len tulong) (Econst_long (Int64.repr 16) tulong) tulong)
       tulong)
    (Econst_long (Int64.repr 19) tulong) tulong.

Definition adler32_z_type : type :=
  Tfunction (tulong :: tptr tuchar :: tulong :: nil) tulong cc_default.

(* Any identifier not used by the Adler-32 file will do. *)
Definition _twice : ident := 900001%positive.

Definition f_twice : function :=
  {| fn_return := tulong; fn_callconv := cc_default;
     fn_params := (_buf, tptr tuchar) :: (_len, tulong) :: nil;
     fn_vars := nil;
     fn_temps := (_adler, tulong) :: (_t'1, tulong) :: (_t'2, tulong) :: nil;
     fn_body :=
       Ssequence (Sassign (Evar _fvz_ticks tulong) budget)
      (Ssequence (Scall (Some _t'1) (Evar _adler32_z adler32_z_type)
                    (Econst_long (Int64.repr 1) tulong
                     :: Etempvar _buf (tptr tuchar)
                     :: Etempvar _len tulong :: nil))
      (Ssequence (Sset _adler (Etempvar _t'1 tulong))
      (Ssequence (Sassign (Evar _fvz_ticks tulong) budget)
      (Ssequence (Scall (Some _t'2) (Evar _adler32_z adler32_z_type)
                    (Etempvar _adler tulong
                     :: Etempvar _buf (tptr tuchar)
                     :: Etempvar _len tulong :: nil))
                 (Sreturn (Some (Etempvar _t'2 tulong))))))) |}.

(** The client asks nothing of its caller about ticks.  It only needs to
    own the counter, whatever value it holds. *)
Definition twice_spec : ident * funspec :=
 DECLARE _twice
  WITH sh : share, bs : list byte, base : val, gv : globals
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; 0 < Zlength bs; Zlength bs < 2 ^ 60)
    PARAMS (base; Vlong (Int64.repr (Zlength bs))) GLOBALS (gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
         data_at_ Ews tulong (gv _fvz_ticks))
  POST [ tulong ]
    EX r : int64,
    PROP ()
    RETURN (Vlong r)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
         data_at_ Ews tulong (gv _fvz_ticks)).

Lemma divu64 a b :
  0 <= a <= Int64.max_unsigned -> 0 < b <= Int64.max_unsigned ->
  Int64.divu (Int64.repr a) (Int64.repr b) = Int64.repr (a / b).
Proof.
  intros. unfold Int64.divu. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* The budget expression evaluates to the cost bound. *)
Lemma budget_value n :
  0 <= n < 2 ^ 60 ->
  Int64.add (Int64.add (Int64.divu (Int64.repr n) (Int64.repr 5552))
                       (Int64.divu (Int64.repr n) (Int64.repr 16)))
            (Int64.repr 19)
  = Int64.repr (adler32_z_cost n).
Proof.
  intros. rewrite !divu64 by rep_lia. rewrite !add64_repr. reflexivity.
Qed.

Lemma cost_in_range n :
  0 <= n < 2 ^ 60 -> 0 <= adler32_z_cost n <= Int64.max_unsigned.
Proof.
  intros. unfold adler32_z_cost.
  pose proof (Z.div_pos n 5552 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos n 16 ltac:(lia) ltac:(lia)).
  assert (n / 5552 <= n) by (apply Z.div_le_upper_bound; lia).
  assert (n / 16 <= n) by (apply Z.div_le_upper_bound; lia).
  rep_lia.
Qed.

Definition Gprog_client : funspecs := [adler32_z_cost_spec; twice_spec].

Lemma body_twice :
  semax_body Vprog_ticks Gprog_client f_twice twice_spec.
Proof.
  start_function. unfold budget.
  pose proof (cost_in_range (Zlength bs) ltac:(lia)) as Hcost.
  forward.
  forward_call (1, sh, bs, base, gv, adler32_z_cost (Zlength bs)).
  { unfold ticks. rewrite budget_value by lia. cancel. }
  Intros vret. destruct vret as [r1 u1]. cbn [fst snd] in *.
  forward.
  (* refill: whatever the first call left is overwritten *)
  unfold ticks. forward.
  pose proof (Int64.unsigned_range_2 r1).
  forward_call (Int64.unsigned r1, sh, bs, base, gv, adler32_z_cost (Zlength bs)).
  { rewrite Int64.repr_unsigned. entailer!. }
  { unfold ticks. rewrite budget_value by lia. cancel. }
  Intros vret. destruct vret as [r2 u2]. cbn [fst snd] in *.
  forward.
  Exists r2. unfold ticks. entailer!.
Qed.

Print Assumptions body_adler32_cost.
