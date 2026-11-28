(** * Adler-32: one statement for the whole file

    The other files prove one contract at a time, each assuming the
    contracts of the functions its function calls.  This file puts them
    together.  [Gprog] lists one contract for each function that
    [adler32.c] defines.  [adler32_c_verified] says that every function
    the file defines has its contract in that list, and that its body
    meets the contract when the functions it calls meet theirs, taken from
    the same list.

    The statement speaks of every function in the translated file, not of
    five named ones.  A function added to [adler32.c] and left without a
    proof would make it fail.

    [adler32_c_verified_with_ticks] says the same of the functions with
    ticks added and the contracts with a cost bound.  It speaks of
    [instrument_function f] for every function [f] the file defines, so it
    covers exactly the code that the instrumentation makes from this file.

    What neither is: a theorem about executions.  Each is the premise of
    VST's rule for linking the functions of a program, not that rule's
    conclusion.  A library does not run by itself, so the step to
    executions is taken for a whole program that calls these functions, in
    [proofs/adler32_client].  It is taken for the contracts without a cost
    bound only. *)

Require Import VST.floyd.proofauto.
From fvzlib.proofs.lib Require Import Ticks TickLogic.
From fvzlib.proofs.adler32 Require Import adler32_clight Spec Contract
  ContractProof Combine Ticked CostContract CombineTicked CostContractProof.

(** The contract of each function defined in [adler32.c]. *)
Definition Gprog : funspecs :=
  [adler32_z_contract; adler32_contract; combine_internal_spec;
   adler32_combine_funspec; adler32_combine64_funspec].

(** A proof that assumes some of the contracts in [Gprog] also holds when
    all of them are assumed. *)
Lemma widen (G : funspecs) (f : function) (spec : ident * funspec) :
  incl G Gprog -> semax_body Vprog G f spec -> semax_body Vprog Gprog f spec.
Proof.
  intros Hincl H. eapply semax_body_subsumption; [exact H |].
  apply semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - exact Hincl.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Ltac listed := intros x Hx; simpl in *; tauto.

(** The five functions, each under the whole list. *)
Lemma each_function :
  semax_body Vprog Gprog f_adler32_z adler32_z_contract /\
  semax_body Vprog Gprog f_adler32 adler32_contract /\
  semax_body Vprog Gprog f_adler32_combine_ combine_internal_spec /\
  semax_body Vprog Gprog f_adler32_combine adler32_combine_funspec /\
  semax_body Vprog Gprog f_adler32_combine64 adler32_combine64_funspec.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - apply (widen []); [listed | apply body_adler32_z].
  - apply (widen [adler32_z_contract]); [listed | apply body_adler32].
  - apply (widen [combine_internal_spec]);
      [listed | apply body_combine_internal].
  - apply (widen [combine_internal_spec; adler32_combine_funspec]);
      [listed | apply body_adler32_combine].
  - apply (widen [combine_internal_spec; adler32_combine64_funspec]);
      [listed | apply body_adler32_combine64].
Qed.

(** Every function that the translated file defines.  [prog] is the whole
    of [adler32.c] as CompCert reads it.  Its other definitions are
    declarations of functions defined elsewhere, which [Internal] leaves
    out. *)
Theorem adler32_c_verified :
  forall (id : ident) (f : function),
    In (id, Gfun (Internal f)) (prog_defs prog) ->
    exists spec : funspec,
      In (id, spec) Gprog /\ semax_body Vprog Gprog f (id, spec).
Proof.
  intros id f Hin.
  destruct each_function as (Hz & Ha & Hi & Hc & Hc64).
  simpl in Hin.
  repeat (destruct Hin as [Hin | Hin]; [try discriminate Hin |]);
    try contradiction;
    injection Hin as <- <-.
  - exists (snd adler32_z_contract). split; [simpl; tauto | exact Hz].
  - exists (snd adler32_contract). split; [simpl; tauto | exact Ha].
  - exists (snd combine_internal_spec). split; [simpl; tauto | exact Hi].
  - exists (snd adler32_combine_funspec). split; [simpl; tauto | exact Hc].
  - exists (snd adler32_combine64_funspec). split; [simpl; tauto | exact Hc64].
Qed.

(** The list has exactly as many contracts as the file has functions. *)
Example five_functions :
  length (filter (fun d => match snd d with
                           | Gfun (Internal _) => true
                           | _ => false
                           end) (prog_defs prog))
  = length Gprog.
Proof. reflexivity. Qed.

(** ** The same for the functions with ticks

    The contract with a cost bound of each function. *)
Definition Gprog_ticked : funspecs :=
  [adler32_z_ticked_contract; adler32_ticked_contract;
   combine_internal_ticked_spec; adler32_combine_ticked_funspec;
   adler32_combine64_ticked_funspec].

Lemma widen_ticked (G : funspecs) (f : function) (spec : ident * funspec) :
  incl G Gprog_ticked ->
  semax_body Vprog_ticks G f spec -> semax_body Vprog_ticks Gprog_ticked f spec.
Proof.
  intros Hincl H. eapply semax_body_subsumption; [exact H |].
  apply semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - exact Hincl.
  - repeat constructor; simpl; intuition discriminate.
Qed.

Lemma each_function_ticked :
  semax_body Vprog_ticks Gprog_ticked f_adler32_z_ticked
             adler32_z_ticked_contract /\
  semax_body Vprog_ticks Gprog_ticked f_adler32_ticked
             adler32_ticked_contract /\
  semax_body Vprog_ticks Gprog_ticked f_adler32_combine__ticked
             combine_internal_ticked_spec /\
  semax_body Vprog_ticks Gprog_ticked f_adler32_combine_ticked
             adler32_combine_ticked_funspec /\
  semax_body Vprog_ticks Gprog_ticked f_adler32_combine64_ticked
             adler32_combine64_ticked_funspec.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - apply (widen_ticked []); [listed | apply body_adler32_z_ticked].
  - apply (widen_ticked [adler32_z_ticked_contract]);
      [listed | apply body_adler32_ticked].
  - apply (widen_ticked []); [listed | apply body_combine_internal_ticked].
  - apply (widen_ticked
             [combine_internal_ticked_spec; adler32_combine_ticked_funspec]);
      [listed | apply body_adler32_combine_ticked].
  - apply (widen_ticked
             [combine_internal_ticked_spec; adler32_combine64_ticked_funspec]);
      [listed | apply body_adler32_combine64_ticked].
Qed.

(** Every function the translated file defines, once instrumented, meets
    its contract with a cost bound. *)
Theorem adler32_c_verified_with_ticks :
  forall (id : ident) (f : function),
    In (id, Gfun (Internal f)) (prog_defs prog) ->
    exists spec : funspec,
      In (id, spec) Gprog_ticked /\
      semax_body Vprog_ticks Gprog_ticked (instrument_function f) (id, spec).
Proof.
  intros id f Hin.
  destruct each_function_ticked as (Hz & Ha & Hi & Hc & Hc64).
  simpl in Hin.
  repeat (destruct Hin as [Hin | Hin]; [try discriminate Hin |]);
    try contradiction;
    injection Hin as <- <-.
  - exists (snd adler32_z_ticked_contract).
    split; [simpl; tauto | rewrite <- ticked_adler32_z; exact Hz].
  - exists (snd adler32_ticked_contract).
    split; [simpl; tauto | rewrite <- ticked_adler32; exact Ha].
  - exists (snd combine_internal_ticked_spec).
    split; [simpl; tauto | rewrite <- ticked_combine_; exact Hi].
  - exists (snd adler32_combine_ticked_funspec).
    split; [simpl; tauto | rewrite <- ticked_combine; exact Hc].
  - exists (snd adler32_combine64_ticked_funspec).
    split; [simpl; tauto | rewrite <- ticked_combine64; exact Hc64].
Qed.
