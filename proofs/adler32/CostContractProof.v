(** * Adler-32: proofs of the contracts with a cost bound (Layer 4)

    Three things are proven here about the contracts of [CostContract.v].

    - **The functions with ticks meet the written contracts.**  For
      [adler32_z] the contract is derived from the three proven in
      [VerifTicked.v], one for each kind of buffer argument, in the way
      [ContractProof.v] derives the plain contract.  [adler32] is proven
      from the contract of [adler32_z].  The combine functions are in
      [CombineTicked.v].
    - **Each written contract says what its generated one says.**  Each
      follows from the other.
    - **Each plain contract and its generated one are two forms of one
      contract**: [two_forms] of one precondition and one postcondition.

    So a function with ticks meets the contract that [with_ticks] makes
    from the plain contract of the function without them. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.lib Require Import Ticks TickLogic.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Buffer
  Spec Verif EmptyBuffer Contract ContractProof Combine Ticked CostContract
  VerifTicked CombineTicked.

(** ** Costs are positive *)

Lemma buffer_cost_bounds len : 0 <= len -> 19 <= buffer_cost len.
Proof.
  intros. unfold buffer_cost.
  pose proof (Z.div_pos len 5552 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos len 16 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma adler32_z_cost_bounds b len : 0 <= len -> 1 <= adler32_z_cost b len.
Proof.
  intros. destruct b; simpl; [lia | pose proof (buffer_cost_bounds len); lia].
Qed.

(** ** Naming what a call returned

    After a call, the value returned and the ticks used are in the
    context.  These tactics give them as witnesses. *)
Ltac pick_used :=
  match goal with |- ?L |-- _ =>
    match L with context [ticks _ (_ - ?u)] => Exists u end end.
Ltac pick_result :=
  first [ match goal with
          | H : Vlong (Int64.repr ?r) = eval_id ret_temp _ |- _ => Exists r
          end
        | match goal with
          | H : Vlong ?r = eval_id ret_temp _ |- _ => Exists r
          end ].
Ltac open_right := repeat first [ rewrite exp_sepcon1 | rewrite exp_andp2 ].
(* A generated contract names the ticks used first, a written one the
   result first. *)
Ltac to_generated :=
  intros ? ? ?; open_right; pick_used; open_right; pick_result; entailer!.
Ltac to_written :=
  intros ? ? ?; open_right; pick_result; open_right; pick_used; entailer!.

(** ** adler32_z *)

Lemma body_adler32_z_ticked :
  semax_body Vprog_ticks [] f_adler32_z_ticked adler32_z_ticked_contract.
Proof.
  unfold adler32_z_ticked_contract.
  apply semax_body_pointwise.
  { constructor. exact (0, Null, Vundef, 0, (fun _ => Vundef), 0). }
  intros [[[[[adler b] base] len] gvs] t].
  destruct b as [| sh before bs after].
  - eapply semax_body_funspec_sub.
    + apply body_adler32_z_null_ticked.
    + do_funspec_sub. Exists (adler, len, gvs, t) emp. simpl. entailer!.
      to_written.
      match goal with H : running_checksum _ [] |- _ => destruct H as [_ ->] end.
      apply adler32_range.
    + prove_lnr.
  - destruct (Z.eq_dec (Zlength bs) 0) as [Hz | Hnz].
    + apply Zlength_nil_inv in Hz. subst bs.
      eapply semax_body_funspec_sub.
      * apply body_adler32_z_empty_ticked.
      * do_funspec_sub. Exists (adler, sh, before, after, base, gvs, t) emp.
        simpl.
        Intros.
        change (buffer_cost (Zlength (@nil byte))) with (buffer_cost 0) in *.
        entailer!.
        to_written.
      * prove_lnr.
    + eapply semax_body_funspec_sub.
      * apply body_adler32_z_buffer_ticked.
      * do_funspec_sub.
        Exists (adler, sh, bs, offset_val (Zlength before) base, gvs, t)
               (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs)
                        (offset_val (Zlength before) base)
                -* data_at sh
                     (tarray tuchar (Zlength (buffer_array before bs after)))
                     (buffer_array before bs after) base).
        sep_apply (run_in_array sh before bs after base).
        simpl. Intros.
        (* the run is not empty, so the caller may read it *)
        assert (Hread : readable_share sh).
        { match goal with H : _ -> readable_share sh |- _ => apply H end.
          intros ->. apply Hnz. reflexivity. }
        entailer!.
        to_written.
        rewrite sepcon_comm. apply modus_ponens_wand.
      * prove_lnr.
Qed.

(** ** adler32

    It spends a tick, calls [adler32_z] with what is left of its budget,
    and returns what that returned. *)

Lemma body_adler32_ticked :
  semax_body Vprog_ticks [adler32_z_ticked_contract] f_adler32_ticked
             adler32_ticked_contract.
Proof.
  start_function. unfold adler32_cost in *.
  pose proof (adler32_z_cost_bounds b len ltac:(lia)) as Hc.
  unfold ticks.
  spend_tick.
  forward_call (adler, b, base, len, gv, t - 1).
  { unfold ticks. rewrite sub64_repr. cancel. }
  Intros vret. destruct vret as [r used]. cbn [fst snd] in *.
  forward.
  Exists r (used + 1). unfold ticks. entailer!.
  apply derives_refl'. do 3 f_equal. lia.
Qed.

(** ** Each written contract says what its generated one says *)

Lemma adler32_z_ticked_gives_generated :
  funspec_sub (snd adler32_z_ticked_contract) adler32_z_generated.
Proof.
  unfold adler32_z_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[[adler b] base] len] gv] t].
  Exists (adler, b, base, len, gv, t) emp. simpl. entailer!. to_generated.
Qed.

Lemma adler32_z_generated_gives_ticked :
  funspec_sub adler32_z_generated (snd adler32_z_ticked_contract).
Proof.
  unfold adler32_z_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[[adler b] base] len] gv] t].
  Exists (adler, b, base, len, gv, t) emp. simpl. entailer!. to_written.
Qed.

Lemma adler32_ticked_gives_generated :
  funspec_sub (snd adler32_ticked_contract) adler32_generated.
Proof.
  unfold adler32_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[[adler b] base] len] gv] t].
  Exists (adler, b, base, len, gv, t) emp. simpl. entailer!. to_generated.
Qed.

Lemma adler32_generated_gives_ticked :
  funspec_sub adler32_generated (snd adler32_ticked_contract).
Proof.
  unfold adler32_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[[adler b] base] len] gv] t].
  Exists (adler, b, base, len, gv, t) emp. simpl. entailer!. to_written.
Qed.

Lemma combine_internal_ticked_gives_generated :
  funspec_sub (snd combine_internal_ticked_spec) combine_internal_generated.
Proof.
  unfold combine_internal_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[adler1 adler2] len2] gv] t].
  Exists (adler1, adler2, len2, gv, t) emp. simpl. entailer!. to_generated.
Qed.

Lemma combine_internal_generated_gives_ticked :
  funspec_sub combine_internal_generated (snd combine_internal_ticked_spec).
Proof.
  unfold combine_internal_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[adler1 adler2] len2] gv] t].
  Exists (adler1, adler2, len2, gv, t) emp. simpl. entailer!. to_written.
Qed.

Lemma adler32_combine_ticked_gives_generated :
  funspec_sub (snd adler32_combine_ticked_funspec) adler32_combine_generated.
Proof.
  unfold adler32_combine_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[adler1 adler2] len2] gv] t].
  Exists (adler1, adler2, len2, gv, t) emp. simpl. entailer!. to_generated.
Qed.

Lemma adler32_combine_generated_gives_ticked :
  funspec_sub adler32_combine_generated (snd adler32_combine_ticked_funspec).
Proof.
  unfold adler32_combine_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[adler1 adler2] len2] gv] t].
  Exists (adler1, adler2, len2, gv, t) emp. simpl. entailer!. to_written.
Qed.

Lemma adler32_combine64_ticked_gives_generated :
  funspec_sub (snd adler32_combine64_ticked_funspec)
              adler32_combine64_generated.
Proof.
  unfold adler32_combine64_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[adler1 adler2] len2] gv] t].
  Exists (adler1, adler2, len2, gv, t) emp. simpl. entailer!. to_generated.
Qed.

Lemma adler32_combine64_generated_gives_ticked :
  funspec_sub adler32_combine64_generated
              (snd adler32_combine64_ticked_funspec).
Proof.
  unfold adler32_combine64_generated, with_ticks.
  do_funspec_sub. destruct w as [[[[adler1 adler2] len2] gv] t].
  Exists (adler1, adler2, len2, gv, t) emp. simpl. entailer!. to_written.
Qed.

(** ** Two forms of one contract

    Each plain contract is made of a precondition and a postcondition.
    Its generated contract is [with_ticks] of the same two. *)

Lemma adler32_z_two_forms :
  two_forms ([tulong; tptr tuchar; tulong], tulong) cc_default
    (Z * buffer_arg * val * Z)
    (fun w => let '(_, b, _, len) := w in adler32_z_cost b len)
    (snd adler32_z_contract) adler32_z_generated.
Proof. eexists. eexists. split; reflexivity. Qed.

Lemma adler32_two_forms :
  two_forms ([tulong; tptr tuchar; tuint], tulong) cc_default
    (Z * buffer_arg * val * Z)
    (fun w => let '(_, b, _, len) := w in adler32_cost b len)
    (snd adler32_contract) adler32_generated.
Proof. eexists. eexists. split; reflexivity. Qed.

Lemma combine_internal_two_forms :
  two_forms ([tulong; tulong; tlong], tulong) cc_default (Z * Z * Z)
    (fun _ => combine_internal_cost)
    (snd combine_internal_spec) combine_internal_generated.
Proof. eexists. eexists. split; reflexivity. Qed.

Lemma adler32_combine_two_forms :
  two_forms ([tulong; tulong; tlong], tulong) cc_default (Z * Z * Z)
    (fun _ => adler32_combine_cost)
    (snd adler32_combine_funspec) adler32_combine_generated.
Proof. eexists. eexists. split; reflexivity. Qed.

Lemma adler32_combine64_two_forms :
  two_forms ([tulong; tulong; tlong], tulong) cc_default (Z * Z * Z)
    (fun _ => adler32_combine_cost)
    (snd adler32_combine64_funspec) adler32_combine64_generated.
Proof. eexists. eexists. split; reflexivity. Qed.

(** ** Nothing was lost

    Each contract for one kind of buffer argument follows from the
    contract of [adler32_z] with ticks. *)

Lemma adler32_z_ticked_contract_gives_null :
  funspec_sub (snd adler32_z_ticked_contract) (snd adler32_z_null_ticked_spec).
Proof.
  do_funspec_sub. destruct w as [[[adler len] gv] t].
  Exists (adler, Null, Vundef, len, gv, t) emp. simpl. entailer!. to_written.
Qed.

Lemma adler32_z_ticked_contract_gives_empty :
  funspec_sub (snd adler32_z_ticked_contract)
              (snd adler32_z_empty_ticked_spec).
Proof.
  do_funspec_sub. destruct w as [[[[[[adler sh] before] after] arr] gv] t].
  Exists (adler, Buffer sh before [] after, arr, 0, gv, t) emp. simpl.
  entailer!. to_written.
Qed.

Lemma adler32_z_ticked_contract_gives_buffer :
  funspec_sub (snd adler32_z_ticked_contract)
              (snd adler32_z_buffer_ticked_spec).
Proof.
  do_funspec_sub. destruct w as [[[[[adler sh] bs] buf] gv] t].
  Exists (adler, Buffer sh [] bs [], buf, Zlength bs, gv, t) emp. simpl.
  rewrite !run_alone, Zlength_map. change (Zlength (@nil val)) with 0.
  Intros.
  assert_PROP (isptr buf) as Hptr by entailer!.
  rewrite isptr_offset_val_zero by assumption.
  assert (Hsome : sepalg.nonidentity sh)
    by (apply readable_nonidentity; assumption).
  entailer!. to_written.
Qed.
