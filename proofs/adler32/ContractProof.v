(** * Adler-32: proofs of the contracts in [Contract.v] (Layer 4)

    The contract of [adler32_z] is not proven against the C code a second
    time.  It is derived from the three contracts already proven for that
    code, one for each kind of buffer argument:

    - a null buffer, in [Verif.v];
    - a non-empty buffer, in [Verif.v];
    - a non-null buffer of length zero, in [EmptyBuffer.v].

    For any one call, the contract in [Contract.v] follows from one of the
    three.  Which one depends on the buffer argument.  VST's rule for
    replacing a contract by one it implies then gives the result for that
    call, and a small lemma collects the calls into one contract.

    The contract also covers a call that none of the three covers directly:
    a non-empty run of bytes inside a larger array.  That follows from the
    contract for a non-empty buffer, because the rest of the array is not
    touched.

    [adler32] passes its arguments to [adler32_z], so its contract is
    proven directly from the contract of [adler32_z].

    Last, each of the narrower contracts is shown to follow from the
    contract here.  Nothing was lost in combining them. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Buffer
  Spec Verif EmptyBuffer Contract.

(** ** Collecting calls into one contract

    A contract holds for a function body if, for each choice of the
    contract's parameters, the contract with those parameters fixed holds.
    This is the definition of [semax_body] read backwards.  It lets a
    proof choose a different argument for each choice of parameters. *)
Lemma semax_body_pointwise V G {cs : compspecs} (f : function) (id : ident)
    sig cc (A : Type)
    (P : A -> argsEnviron -> mpred) (Q : A -> environ -> mpred) :
  inhabited A ->
  (forall w : A,
     semax_body V G f
       (id, NDmk_funspec sig cc unit (fun _ => P w) (fun _ => Q w))) ->
  semax_body V G f (id, NDmk_funspec sig cc A P Q).
Proof.
  intros [w0] H. unfold semax_body, NDmk_funspec in *.
  destruct (H w0) as (H1 & H2 & _).
  split; [exact H1 | split; [exact H2 |]].
  intros Espec ts x. destruct (H x) as (_ & _ & Hx). exact (Hx Espec ts tt).
Qed.

(** A run of bytes inside a larger array can be handed over on its own.
    What is left is enough to put the array back together. *)
Lemma run_in_array sh (before bs after : list byte) (base : val) :
  data_at sh (tarray tuchar (Zlength (before ++ bs ++ after)))
          (map Vubyte (before ++ bs ++ after)) base
  |-- data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs)
              (offset_val (Zlength before) base) *
      (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs)
               (offset_val (Zlength before) base)
       -* data_at sh (tarray tuchar (Zlength (before ++ bs ++ after)))
                  (map Vubyte (before ++ bs ++ after)) base).
Proof.
  set (all := before ++ bs ++ after).
  pose proof (Zlength_nonneg before) as Hb.
  pose proof (Zlength_nonneg bs) as Hm.
  pose proof (Zlength_nonneg after) as Ha.
  assert (Hall : Zlength all = Zlength before + (Zlength bs + Zlength after))
    by (subst all; rewrite !Zlength_app; lia).
  saturate_local.
  rewrite (buffer_split_eq sh all base (Zlength before)) by (auto; lia).
  replace (sublist (Zlength before) (Zlength all) all) with (bs ++ after)
    by (subst all; list_solve).
  replace (Zlength all - Zlength before) with (Zlength (bs ++ after))
    by (rewrite Zlength_app; lia).
  saturate_local.
  rewrite (buffer_split_eq sh (bs ++ after) (offset_val (Zlength before) base)
             (Zlength bs)) by (auto; rewrite Zlength_app; lia).
  replace (sublist 0 (Zlength bs) (bs ++ after)) with bs by list_solve.
  match goal with |- (?L * (?M * ?R))%logic |-- _ =>
    apply derives_trans with (M * (L * R))%logic; [cancel |];
    apply sepcon_derives;
      [apply derives_refl | rewrite <- wand_sepcon_adjoint; cancel]
  end.
Qed.

(** A function's parameters and local variables have distinct names. *)
Ltac prove_lnr :=
  compute; repeat constructor;
  let Hin := fresh in intros Hin; simpl in Hin; decompose [or] Hin;
  try discriminate; contradiction.

(** ** adler32_z *)

Lemma body_adler32_z :
  semax_body Vprog [] f_adler32_z adler32_z_contract.
Proof.
  unfold adler32_z_contract.
  apply semax_body_pointwise.
  { constructor. exact (0, Null, Vundef, 0). }
  intros [[[adler b] base] len].
  destruct b as [| sh before bs after].
  - eapply semax_body_funspec_sub.
    + apply body_adler32_z_null.
    + do_funspec_sub. Exists (adler, len) emp. simpl. entailer!.
      intros rho' _ Hret. Exists x0. entailer!.
      match goal with H : running_checksum _ [] |- _ => destruct H as [_ ->] end.
      apply adler32_range.
    + prove_lnr.
  - destruct (Z.eq_dec (Zlength bs) 0) as [Hz | Hnz].
    + apply Zlength_nil_inv in Hz. subst bs.
      eapply semax_body_funspec_sub.
      * apply body_adler32_z_empty.
      * do_funspec_sub. Exists (adler, sh, before, after, base) emp.
        simpl. entailer!.
        intros rho' _ Hret. Exists x0. entailer!.
      * prove_lnr.
    + eapply semax_body_funspec_sub.
      * apply body_adler32_z_buffer.
      * do_funspec_sub.
        Exists (adler, sh, bs, offset_val (Zlength before) base)
               (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs)
                        (offset_val (Zlength before) base)
                -* data_at sh (tarray tuchar (Zlength (before ++ bs ++ after)))
                           (map Vubyte (before ++ bs ++ after)) base).
        sep_apply (run_in_array sh before bs after base).
        simpl. entailer!.
        intros rho' _ Hret. Exists x0. entailer!.
        rewrite sepcon_comm. apply modus_ponens_wand.
      * prove_lnr.
Qed.

(** ** adler32 *)

Lemma body_adler32 :
  semax_body Vprog [adler32_z_contract] f_adler32 adler32_contract.
Proof.
  start_function.
  forward_call (adler, b, base, len).
  Intros r. forward. Exists r. entailer!.
Qed.

(** ** Nothing was lost

    Each narrower contract follows from the contract in [Contract.v]. *)

Lemma adler32_z_contract_gives_null :
  funspec_sub (snd adler32_z_contract) (snd adler32_z_null_spec).
Proof.
  do_funspec_sub. destruct w as [adler len].
  Exists (adler, Null, Vundef, len) emp. simpl. entailer!.
  intros rho' _ Hret. Exists x0. entailer!.
Qed.

Lemma adler32_z_contract_gives_empty :
  funspec_sub (snd adler32_z_contract) (snd adler32_z_empty_spec).
Proof.
  do_funspec_sub. destruct w as [[[[adler sh] before] after] arr].
  Exists (adler, Buffer sh before [] after, arr, 0) emp. simpl. entailer!.
  intros rho' _ Hret. Exists x0. entailer!.
Qed.

Lemma adler32_z_contract_gives_buffer :
  funspec_sub (snd adler32_z_contract) (snd adler32_z_buffer_spec).
Proof.
  do_funspec_sub. destruct w as [[[adler sh] bs] buf].
  Exists (adler, Buffer sh [] bs [], buf, Zlength bs) emp. simpl.
  rewrite !app_nil_r. change (Zlength (@nil byte)) with 0.
  Intros.
  assert_PROP (isptr buf) as Hptr by entailer!.
  rewrite isptr_offset_val_zero by assumption.
  entailer!.
  intros rho' _ Hret. Exists x0. entailer!.
Qed.

(** The same for [adler32]. *)

Lemma adler32_contract_gives_null :
  funspec_sub (snd adler32_contract) (snd adler32_null_spec).
Proof.
  do_funspec_sub. destruct w as [adler len].
  Exists (adler, Null, Vundef, len) emp. simpl. entailer!.
  intros rho' _ Hret. Exists x0. entailer!.
Qed.

Lemma adler32_contract_gives_empty :
  funspec_sub (snd adler32_contract) (snd adler32_empty_spec).
Proof.
  do_funspec_sub. destruct w as [[[[adler sh] before] after] arr].
  Exists (adler, Buffer sh before [] after, arr, 0) emp. simpl. entailer!.
  intros rho' _ Hret. Exists x0. entailer!.
Qed.

Lemma adler32_contract_gives_buffer :
  funspec_sub (snd adler32_contract) (snd adler32_buffer_spec).
Proof.
  do_funspec_sub. destruct w as [[[adler sh] bs] buf].
  Exists (adler, Buffer sh [] bs [], buf, Zlength bs) emp. simpl.
  rewrite !app_nil_r. change (Zlength (@nil byte)) with 0.
  Intros.
  assert_PROP (isptr buf) as Hptr by entailer!.
  rewrite isptr_offset_val_zero by assumption.
  entailer!.
  intros rho' _ Hret. Exists x0. entailer!.
Qed.
