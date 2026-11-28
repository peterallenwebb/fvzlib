(** * Spike: a client that refills the counter between two calls

    A caller of a function with ticks has to hand it a budget.  The
    contracts in [proofs/adler32/CostContract.v] let the caller pass on a
    budget it was given.  This file tries the other way: a client that
    sets the counter itself before each call, and so asks nothing of its
    own caller about ticks.

    The client is proven against the contract of [adler32_z] with ticks
    from the main proofs, and against nothing else.

    It is exploratory.  The statement that erasing the ticks preserves
    behavior, in [proofs/lib/TickStatements.v], does not cover a program
    that sets the counter like this, since that assignment is
    instrumentation too and the transformation does not add it. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.lib Require Import Ticks TickLogic.
From fvzlib.proofs.adler32 Require Import adler32_clight Spec Contract
  ContractProof CostContract.

(** <<
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
    EX r : Z,
    PROP (0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
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
  = Int64.repr (buffer_cost n).
Proof.
  intros. rewrite !divu64 by rep_lia. rewrite !add64_repr. reflexivity.
Qed.

Lemma cost_in_range n :
  0 <= n < 2 ^ 60 -> 0 <= buffer_cost n <= Int64.max_unsigned.
Proof.
  intros. unfold buffer_cost.
  pose proof (Z.div_pos n 5552 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos n 16 ltac:(lia) ltac:(lia)).
  assert (n / 5552 <= n) by (apply Z.div_le_upper_bound; lia).
  assert (n / 16 <= n) by (apply Z.div_le_upper_bound; lia).
  rep_lia.
Qed.

(** The whole of the client's buffer, as the contract takes it. *)
Definition whole (sh : share) (bs : list byte) : buffer_arg := Buffer sh [] bs [].

Lemma whole_rep sh bs base :
  buffer_rep (whole sh bs) base =
  data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base.
Proof. simpl. rewrite run_alone, Zlength_map. reflexivity. Qed.

Lemma whole_ok sh bs :
  readable_share sh -> 0 < Zlength bs -> buffer_ok (whole sh bs) (Zlength bs).
Proof.
  intros. split; [reflexivity |].
  split; [apply readable_nonidentity; assumption |].
  split; [auto |]. rewrite run_alone, Zlength_map. assumption.
Qed.

Definition Gprog_client : funspecs := [adler32_z_ticked_contract; twice_spec].

Lemma body_twice :
  semax_body Vprog_ticks Gprog_client f_twice twice_spec.
Proof.
  start_function. unfold budget.
  pose proof (cost_in_range (Zlength bs) ltac:(lia)) as Hcost.
  forward.
  forward_call (1, whole sh bs, base, Zlength bs, gv, buffer_cost (Zlength bs)).
  { entailer!. simpl. rewrite isptr_offset_val_zero by auto. reflexivity. }
  { rewrite whole_rep. unfold ticks. rewrite budget_value by lia. cancel. }
  { split; [apply whole_ok; assumption | simpl; lia]. }
  Intros vret. destruct vret as [r1 u1]. cbn [fst snd] in *.
  rewrite whole_rep.
  forward.
  (* refill: whatever the first call left is overwritten *)
  unfold ticks. forward.
  forward_call (r1, whole sh bs, base, Zlength bs, gv, buffer_cost (Zlength bs)).
  { entailer!. simpl. rewrite isptr_offset_val_zero by auto. reflexivity. }
  { rewrite whole_rep. unfold ticks. rewrite budget_value by lia. cancel. }
  { split; [apply whole_ok; assumption | simpl; lia]. }
  Intros vret. destruct vret as [r2 u2]. cbn [fst snd] in *.
  rewrite whole_rep.
  forward.
  Exists r2. unfold ticks. entailer!.
Qed.
