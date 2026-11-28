(** * A whole program that calls [adler32.c], and how it runs

    The proofs in [proofs/adler32] are statements in VST's logic about one
    function at a time.  This file takes them to a statement about
    executions, for one program.

    The program is [client.c].  Its [main] calls the four public functions
    of [adler32.c], and two of those call the internal one.  [client.c]
    includes [adler32.c], so clightgen translates them as one program.

    What is proven, in order:

    - The five functions come out of that translation exactly as they do
      when [adler32.c] is translated alone.  So the proofs in
      [proofs/adler32] are about the same functions.
    - [main] meets its contract, using only the contracts of the functions
      it calls.  Every call it makes meets its callee's precondition.
    - The whole program is verified in VST's sense: [client_verified].
    - [client_never_goes_wrong]: no behavior of the program, in CompCert's
      semantics of Clight, is a wrong one.

    The last step uses [proofs/lib/Soundness.v], which says what it takes
    from VST and what it adds.  It holds under two hypotheses about
    external calls, which are in the statement.  This program makes no
    external call, but the theorems it rests on are about all programs.

    The limits.  This is one program and seven calls.  It says nothing
    about another caller.  It says the program does not get stuck: nothing
    about the values computed reaches the statement about executions.  And
    the program is one translation unit, so nothing here is about linking
    separately compiled files. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.lib Require Import Executions Soundness.
From fvzlib.proofs.adler32 Require adler32_clight.
From fvzlib.proofs.adler32 Require Import Spec Contract Combine WholeFile.
From fvzlib.proofs.adler32_client Require Import client_clight.

(** ** The same five functions *)

(** Each is equal, as a syntax tree, to the one the proofs are about. *)

Example same_adler32_z : f_adler32_z = adler32_clight.f_adler32_z.
Proof. reflexivity. Qed.
Example same_adler32 : f_adler32 = adler32_clight.f_adler32.
Proof. reflexivity. Qed.
Example same_combine_internal :
  f_adler32_combine_ = adler32_clight.f_adler32_combine_.
Proof. reflexivity. Qed.
Example same_adler32_combine :
  f_adler32_combine = adler32_clight.f_adler32_combine.
Proof. reflexivity. Qed.
Example same_adler32_combine64 :
  f_adler32_combine64 = adler32_clight.f_adler32_combine64.
Proof. reflexivity. Qed.

(** ** Contracts for the whole program *)

#[export] Instance ClientCompSpecs : compspecs. make_compspecs prog. Defined.
Definition ClientVprog : varspecs. mk_varspecs prog. Defined.

Example same_varspecs : ClientVprog = Spec.Vprog.
Proof. reflexivity. Qed.

(** [main] takes what VST gives the first function of a program, and
    returns 0. *)
Definition main_spec : ident * funspec :=
 DECLARE _main
  WITH gv : globals
  PRE [] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0)) SEP (TT).

(** The five contracts of [adler32.c], the contract of [main], and VST's
    empty contract for each of CompCert's built-in functions. *)
Definition ClientGprog : funspecs :=
  ltac:(with_library prog
    [adler32_z_contract; adler32_contract; combine_internal_spec;
     adler32_combine_funspec; adler32_combine64_funspec; main_spec]).

(** A proof that assumes the five contracts also holds when the whole
    list of the client is assumed. *)
Lemma widen_client (f : function) (spec : ident * funspec) :
  semax_body Spec.Vprog WholeFile.Gprog f spec ->
  semax_body ClientVprog ClientGprog f spec.
Proof.
  intros H. eapply semax_body_subsumption; [exact H |].
  apply semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - intros x Hx. simpl in Hx. unfold ClientGprog. simpl. tauto.
  - apply list_norepet_NoDup. apply compute_list_norepet_e. reflexivity.
Qed.

Lemma body_adler32_z :
  semax_body ClientVprog ClientGprog f_adler32_z adler32_z_contract.
Proof. apply widen_client. exact (proj1 each_function). Qed.

(** ** The proof of [main] *)

(** The nine bytes [main] writes, and the two pieces it passes. *)
Definition wiki_head : list byte := map Byte.repr [87; 105; 107; 105].
Definition wiki_tail : list byte := map Byte.repr [112; 101; 100; 105; 97].
Definition wiki : list byte := wiki_head ++ wiki_tail.

(** The three ways [main] presents its array to a call: the whole of it,
    the first four bytes with the rest behind, and the last five with the
    rest in front. *)
Definition whole_buffer := Buffer Tsh [] wiki [].
Definition head_buffer := Buffer Tsh [] wiki_head (map Vubyte wiki_tail).
Definition tail_buffer := Buffer Tsh (map Vubyte wiki_head) wiki_tail [].

Lemma whole_rep v :
  buffer_rep whole_buffer v = data_at Tsh (tarray tuchar 9) (map Vubyte wiki) v.
Proof. reflexivity. Qed.
Lemma head_rep v :
  buffer_rep head_buffer v = data_at Tsh (tarray tuchar 9) (map Vubyte wiki) v.
Proof. reflexivity. Qed.
Lemma tail_rep v :
  buffer_rep tail_buffer v = data_at Tsh (tarray tuchar 9) (map Vubyte wiki) v.
Proof. reflexivity. Qed.

Ltac buffer_fits :=
  split; [reflexivity |];
  split; [apply readable_nonidentity; apply readable_share_top |];
  split; [intros _; apply readable_share_top | reflexivity].

Lemma body_main : semax_body ClientVprog ClientGprog f_main main_spec.
Proof.
  start_function.
  do 9 forward.
  match goal with
  | |- context [data_at Tsh (tarray tuchar 9) ?c v_data] =>
      replace c with (map Vubyte wiki) by reflexivity
  end.
  forward_call (0, Null, v_data, 0).
  { simpl buffer_rep. cancel. }
  Intros start. simpl buffer_rep.
  forward_call (start, whole_buffer, v_data, 9).
  { buffer_fits. }
  Intros whole.
  forward_call (start, whole_buffer, v_data, 9).
  { buffer_fits. }
  Intros again. rewrite whole_rep, <- head_rep.
  forward_call (start, head_buffer, v_data, 4).
  { buffer_fits. }
  Intros first. rewrite head_rep, <- tail_rep.
  forward_call (start, tail_buffer, v_data, 5).
  { buffer_fits. }
  Intros second. rewrite tail_rep.
  forward_call (first, second, 5).
  Intros both.
  forward_call (first, second, 5).
  Intros wide.
  forward.
  cancel.
Qed.

(** ** The whole program *)

Lemma body_adler32 :
  semax_body ClientVprog ClientGprog f_adler32 adler32_contract.
Proof. apply widen_client. exact (proj1 (proj2 each_function)). Qed.

Lemma body_combine_internal :
  semax_body ClientVprog ClientGprog f_adler32_combine_ combine_internal_spec.
Proof. apply widen_client. exact (proj1 (proj2 (proj2 each_function))). Qed.

Lemma body_adler32_combine :
  semax_body ClientVprog ClientGprog f_adler32_combine adler32_combine_funspec.
Proof.
  apply widen_client. exact (proj1 (proj2 (proj2 (proj2 each_function)))).
Qed.

Lemma body_adler32_combine64 :
  semax_body ClientVprog ClientGprog f_adler32_combine64
    adler32_combine64_funspec.
Proof.
  apply widen_client. exact (proj2 (proj2 (proj2 (proj2 each_function)))).
Qed.

#[local] Existing Instance NullExtension.Espec.

Lemma client_verified : semax_prog prog tt ClientVprog ClientGprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_adler32_z.
  semax_func_cons body_adler32.
  semax_func_cons body_combine_internal.
  semax_func_cons body_adler32_combine.
  semax_func_cons body_adler32_combine64.
  semax_func_cons body_main.
Qed.

(** ** What follows for executions *)

(** The program has no global variable, so its initial memory exists. *)
Lemma client_starts : exists m, Genv.init_mem prog = Some m.
Proof.
  apply Genv.init_mem_exists. intros id v Hin.
  assert (F : forallb (fun d : ident * globdef Clight.fundef type =>
                         match snd d with Gfun _ => true | Gvar _ => false end)
                (AST.prog_defs prog) = true) by reflexivity.
  rewrite forallb_forall in F. specialize (F _ Hin). discriminate.
Qed.

(** The client program never goes wrong, in CompCert's semantics of
    Clight, given the two hypotheses about external calls. *)
Theorem client_never_goes_wrong :
  more_permission_same_call -> inline_calls_deterministic ->
  never_goes_wrong prog.
Proof.
  intros Jsub det. destruct client_starts as (m0 & Hm).
  pose proof client_verified as V.
  apply SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.semax_prog_sound
    in V.
  eapply (verified_program_never_goes_wrong Jsub det prog _ _ m0 f_main V Hm).
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
