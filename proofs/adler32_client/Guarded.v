(** * The client with the guarded function, and what T0003 gives

    [proofs/adler32/CombineGuarded.v] proves the internal combine function
    with a test put in front of its signed remainder.  The test jumps to a
    label that does not exist if the operand is negative, so the proof
    shows the operand is never negative, in the function with the test.

    This file carries that to the function as written, for the client
    program.

    - [guarded_prog] is the client with that one function replaced.  It is
      what the transformation in [proofs/lib/Guard.v] makes of the whole
      client: [guarded_prog_is_the_transformation].  So [main] and the
      other four functions have nothing to guard.
    - The guarded client is verified in VST, and so never goes wrong:
      [guarded_never_goes_wrong].
    - By [guards_removed], the theorem recorded in the ledger as T0003,
      no test the transformation would insert ever comes out true in the
      client as written: [client_tests_never_true].
    - For the one test there is: whenever the client is about to run
      [len2 %= BASE], [len2] is not negative:
      [remainder_operand_not_negative].

    The hypotheses and limits are those of [Client.v]. *)

Require Import VST.floyd.proofauto.
From compcert Require Import Smallstep.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.lib Require Import Census Guard Executions Soundness GuardSound.
From fvzlib.proofs.adler32 Require adler32_clight.
From fvzlib.proofs.adler32 Require Import Spec Contract Combine WholeFile
  CombineGuarded.
From fvzlib.proofs.adler32_client Require Import client_clight Client.

(** ** The client with the guarded function *)

(** The definitions of the client, with the internal combine function
    replaced by its guarded form. *)
Ltac swap_combine l :=
  lazymatch l with
  | (?id, Gfun (Internal f_adler32_combine_)) :: ?rest =>
      constr:((id, Gfun (Internal f_adler32_combine__guarded)) :: rest)
  | ?d :: ?rest => let r := swap_combine rest in constr:(d :: r)
  end.

Definition guarded_definitions : list (ident * globdef Clight.fundef type) :=
  ltac:(let l := eval unfold global_definitions in global_definitions in
        let r := swap_combine l in exact r).

Definition guarded_prog : Clight.program :=
  Clightdefs.mkprogram composites guarded_definitions public_idents _main
    Logic.I.

Example guarded_prog_is_the_transformation :
  guard_program prog = Some guarded_prog.
Proof. vm_compute. reflexivity. Qed.

Example guarded_prog_labels : labels_new guarded_prog = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The guarded client is verified *)

Lemma body_combine_internal_guarded_client :
  semax_body ClientVprog ClientGprog f_adler32_combine__guarded
    combine_internal_spec.
Proof.
  apply widen_client. apply (WholeFile.widen [combine_internal_spec]).
  - intros x Hx. simpl in *. tauto.
  - apply body_combine_internal_guarded.
Qed.

#[local] Existing Instance NullExtension.Espec.

Lemma guarded_verified : semax_prog guarded_prog tt ClientVprog ClientGprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_adler32_z.
  semax_func_cons body_adler32.
  semax_func_cons body_combine_internal_guarded_client.
  semax_func_cons body_adler32_combine.
  semax_func_cons body_adler32_combine64.
  semax_func_cons body_main.
Qed.

(** ** What follows for executions *)

Lemma guarded_starts : exists m, Genv.init_mem guarded_prog = Some m.
Proof.
  apply Genv.init_mem_exists. intros id v Hin.
  assert (F : forallb (fun d : ident * globdef Clight.fundef type =>
                         match snd d with Gfun _ => true | Gvar _ => false end)
                (AST.prog_defs guarded_prog) = true) by reflexivity.
  rewrite forallb_forall in F. specialize (F _ Hin). discriminate.
Qed.

(** The client with the guarded function never goes wrong. *)
Theorem guarded_never_goes_wrong :
  more_permission_same_call -> inline_calls_deterministic ->
  never_goes_wrong guarded_prog.
Proof.
  intros Jsub det. destruct guarded_starts as (m0 & Hm).
  pose proof guarded_verified as V.
  apply SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.semax_prog_sound
    in V.
  eapply (verified_program_never_goes_wrong Jsub det guarded_prog _ _ m0
            f_main V Hm).
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** So in the client as written, with no guard, no test the
    transformation would insert ever comes out true. *)
Theorem client_tests_never_true :
  more_permission_same_call -> inline_calls_deterministic ->
  forall s, Executions.reachable prog s -> no_violation (Clight.globalenv prog) s.
Proof.
  intros Jsub det s R.
  eapply (guards_removed prog guarded_prog
            guarded_prog_is_the_transformation guarded_prog_labels
            (guarded_never_goes_wrong Jsub det)).
  exact R.
Qed.

(** ** The remainder in the internal combine function *)

(** The statement [len2 %= BASE], as clightgen translates it. *)
Definition remainder : statement :=
  Sset _len2
    (Ebinop Omod (Etempvar _len2 tlong) (Econst_int (Int.repr 65521) tuint)
       tlong).

(** The test the transformation puts in front of it: [len2 < 0]. *)
Example remainder_test ret :
  tests ret remainder =
  Some [Ebinop Olt (Etempvar _len2 tlong) (Econst_int (Int.repr 0) tint) tint].
Proof. reflexivity. Qed.

(** Whenever the client is about to run that statement, [len2] holds a
    64-bit integer that is not negative. *)
Theorem remainder_operand_not_negative :
  more_permission_same_call -> inline_calls_deterministic ->
  forall f k e le m,
    Executions.reachable prog (State f remainder k e le m) ->
    exists n, Maps.PTree.get _len2 le = Some (Vlong n) /\ 0 <= Int64.signed n.
Proof.
  intros Jsub det f k e le m R.
  pose proof (client_tests_never_true Jsub det _ R) as N. simpl in N.
  specialize (N _ (remainder_test (fn_return f))).
  inv N. destruct H1 as (v & E & B).
  inv E; [| match goal with H : Clight.eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H end].
  repeat match goal with
  | H : Clight.eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inv H
  | H : Clight.eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => inv H
  | H : Clight.eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H
  end.
  match goal with
  | H : Cop.sem_binary_operation _ _ ?v1 _ _ _ _ = Some _ |- _ =>
      unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith in H;
      simpl in H; destruct v1; simpl in H; try discriminate; inv H
  end.
  eexists. split; [eassumption |].
  assert (Z0 : Int64.signed (Int64.repr (Int.signed (Int.repr 0))) = 0)
    by reflexivity.
  unfold Int64.lt in B. rewrite Z0 in B.
  destruct (zlt (Int64.signed i) 0) as [L | L]; [| lia].
  vm_compute in B. discriminate.
Qed.
