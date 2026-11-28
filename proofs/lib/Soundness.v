(** * From VST's soundness theorem to CompCert's "never goes wrong"

    A VST proof is a statement in VST's program logic.  VST's soundness
    theorem turns a proof of a whole program into a statement about how
    the program runs.  This file applies that theorem and restates its
    conclusion in the terms CompCert uses for its own theorems:
    [never_goes_wrong], no behavior of the program is a wrong one.

    The result is [verified_program_never_goes_wrong].  It is about any
    program, not about zlib.

    VST's theorem does not give this as it stands.  Four things had to be
    added, and each is visible in the statement or in what it depends on.

    - Two hypotheses about external calls.  VST's theorem takes the
      first, [more_permission_same_call], and VST does not prove it.  We
      add the second, [inline_calls_deterministic].  VST's theorem says
      that some execution is safe.  CompCert's notion asks it of every
      execution, and the two agree only where a step has one outcome.
      Both hypotheses are about calls to built-in and external functions.
      Neither is proven here, and each restricts two things CompCert
      leaves undefined: what an external function does, and what inline
      assembly does.
    - Two more axioms.  VST's theorem depends on
      [Clight_core.inline_external_call_mem_events], which VST assumes,
      and on CompCert's [Axioms.proof_irr].  So does this result.
    - That [main] returns an integer.  CompCert calls a program finished
      when [main] returns an integer.  VST calls it finished when [main]
      returns anything.  [main_returns_an_int] closes the difference for
      a [main] of a simple shape, checked by [plain] and [returns]: no
      loop, no jump, no [switch], and no path to its end without a
      [return] of a value.  It holds on a target with 64-bit pointers.
    - That CompCert's step and VST's step agree.  VST's theorem speaks of
      its own copy of the step relation.  [step2_after_core_step] shows
      that where VST's copy steps, CompCert's relation can only go to the
      same state.

    The semantics is [Clight.semantics2], in which parameters are
    temporaries.  It is the one clightgen's output is written for. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Values Memory
  Events Globalenvs Smallstep Behaviors Clight Maps Clightdefs.
Require Import VST.sepcomp.extspec VST.sepcomp.step_lemmas VST.sepcomp.semantics.
Require Import VST.veric.juicy_extspec VST.veric.juicy_mem VST.veric.compspecs
  VST.veric.semax_prog VST.veric.SequentialClight VST.veric.Clight_lemmas.
Require VST.veric.NullExtension VST.veric.Clight_core VST.veric.semax.
From fvzlib.proofs.lib Require Import Executions.
Import ListNotations.

Module Core := VST.veric.Clight_core.

(** ** The two hypotheses about external calls

    The first is the hypothesis of VST's own theorem, word for word.  An
    external call that CompCert may expand inline gives the same result,
    and touches memory in the same way, when the memory it runs on grants
    more permissions. *)
Definition more_permission_same_call : Prop :=
  forall ef se lv m t v m' (EFI : ef_inline ef = true) m1
    (EFC : external_call ef se lv m t v m'), mem_sub m m1 ->
  exists m1' (EFC1 : external_call ef se lv m1 t v m1'),
    mem_sub m' m1' /\
    proj1_sig (Core.inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC1) =
    proj1_sig (Core.inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC).

(** The second is ours.  An external call that VST's semantics executes
    as a step has one result.  VST executes a call as a step when CompCert
    may expand it inline and VST's own list marks it deterministic. *)
Definition inline_calls_deterministic : Prop :=
  forall ef, ef_inline ef && Core.ef_deterministic ef = true ->
  forall (ge : Senv.t) args m t1 t2 v1 v2 m1 m2,
    external_call ef ge args m t1 v1 m1 ->
    external_call ef ge args m t2 v2 m2 ->
    (v1, m1) = (v2, m2).

(** ** CompCert's step agrees with VST's *)

Ltac same :=
  repeat match goal with
  | H1 : eval_expr ?ge ?e ?le ?m ?a _, H2 : eval_expr ?ge ?e ?le ?m ?a _ |- _ =>
      pose proof (eval_expr_fun H1 H2); subst; clear H2
  | H1 : eval_lvalue ?ge ?e ?le ?m ?a _ _ _,
    H2 : eval_lvalue ?ge ?e ?le ?m ?a _ _ _ |- _ =>
      let E := fresh in
      pose proof (eval_lvalue_fun H1 H2) as E; inv E; clear H2
  | H1 : eval_exprlist ?ge ?e ?le ?m ?a ?ty _,
    H2 : eval_exprlist ?ge ?e ?le ?m ?a ?ty _ |- _ =>
      pose proof (eval_exprlist_fun H1 H2); subst; clear H2
  | H1 : assign_loc ?ge ?ty ?m ?b ?o ?bf ?v _,
    H2 : assign_loc ?ge ?ty ?m ?b ?o ?bf ?v _ |- _ =>
      pose proof (assign_loc_fun H1 H2); subst; clear H2
  | H1 : ?x = Some _, H2 : ?x = Some _ |- _ =>
      rewrite H1 in H2; inv H2
  | H1 : ?x = fun_case_f _ _ _, H2 : ?x = fun_case_f _ _ _ |- _ =>
      rewrite H1 in H2; inv H2
  end.

Lemma step2_after_core_step (det : inline_calls_deterministic) ge q m q1 m1 t s' :
  Core.step ge q m q1 m1 ->
  Clight.step2 ge (Core.CC_core_to_CC_state q m) t s' ->
  s' = Core.CC_core_to_CC_state q1 m1.
Proof.
  intros Hc Hs. unfold step2 in Hs.
  inv Hc; simpl in Hs; inv Hs; simpl; same; try reflexivity.
  all: try (match goal with H : _ \/ _ |- _ => destruct H; discriminate end).
  all: try contradiction.
  - match goal with
    | H1 : external_call _ _ _ _ _ _ _, H2 : external_call _ _ _ _ _ _ _ |- _ =>
        pose proof (det _ ltac:(eassumption) _ _ _ _ _ _ _ _ _ H1 H2) as E; inv E
    end.
    reflexivity.
  - match goal with
    | H1 : function_entry2 _ _ _ _ _ _ _, H2 : function_entry2 _ _ _ _ _ _ _ |- _ =>
        inv H1; inv H2
    end.
    match goal with
    | H1 : alloc_variables _ _ _ _ _ _, H2 : alloc_variables _ _ _ _ _ _ |- _ =>
        pose proof (alloc_variables_fun H1 H2) as E; inv E
    end.
    same. reflexivity.
  - match goal with
    | H1 : external_call _ _ _ _ _ _ _, H2 : external_call _ _ _ _ _ _ _ |- _ =>
        pose proof (det _ ltac:(eassumption) _ _ _ _ _ _ _ _ _ H1 H2) as E; inv E
    end.
    reflexivity.
Qed.

(** ** [main] returns an integer

    The statements a [main] may be made of for this result: assignments,
    calls, sequences, tests, and returns of a value. *)
Fixpoint plain (s : statement) : bool :=
  match s with
  | Sskip | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _ => true
  | Ssequence a b => plain a && plain b
  | Sifthenelse _ a b => plain a && plain b
  | Sreturn (Some _) => true
  | _ => false
  end.

(** The statement cannot finish without returning a value. *)
Fixpoint returns (s : statement) : bool :=
  match s with
  | Sreturn (Some _) => true
  | Ssequence a b => returns a || returns b
  | Sifthenelse _ a b => returns a && returns b
  | _ => false
  end.

(** What is left to do in [main]: plain statements only. *)
Fixpoint main_cont (k : cont) : Prop :=
  match k with
  | Kstop => True
  | Kseq s k' => plain s = true /\ main_cont k'
  | _ => False
  end.

(** Some statement still to come returns a value. *)
Fixpoint guarded (k : cont) : Prop :=
  match k with
  | Kseq s k' => returns s = true \/ guarded k'
  | _ => False
  end.

(** A value converted to [int] is an integer.  This uses that a pointer
    does not fit in an [int], which holds where pointers are 64 bits. *)
Lemma cast_to_int v ty m v' :
  sem_cast v ty tint m = Some v' -> exists i, v' = Vint i.
Proof.
  intros H. apply cast_val_is_casted in H. unfold tint in H. inv H; eauto. discriminate.
Qed.

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_labeled_statements_ind
  from statement_ind2, labeled_statements_ind2.

Section MAIN.
Variable fmain : function.
Hypothesis main_int : fn_return fmain = tint.
Hypothesis main_plain : plain (fn_body fmain) = true.
Hypothesis main_returns : returns (fn_body fmain) = true.

(** The stack of calls, when control is in a function that [main] called,
    directly or not: at its bottom is [main], waiting, with a return of a
    value still to come. *)
Fixpoint above_main (k : cont) : Prop :=
  match k with
  | Kstop => False
  | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' => above_main k'
  | Kcall _ f _ _ k' => (f = fmain /\ main_cont k' /\ guarded k') \/ above_main k'
  end.

(** The invariant.  Control is in [main], which has a return of a value
    ahead of it, or above it.  If [main] has returned, it returned an
    integer. *)
Definition main_inv (s : state) : Prop :=
  match s with
  | State f st k _ _ _ =>
      (f = fmain /\ plain st = true /\ main_cont k /\
       (returns st = true \/ guarded k)) \/ above_main k
  | Callstate fd _ k _ => (fd = Internal fmain /\ k = Kstop) \/ above_main k
  | Returnstate v k _ => (k = Kstop /\ exists i, v = Vint i) \/ above_main k
  end.

Lemma above_call_cont k : above_main k -> above_main (call_cont k).
Proof. induction k; simpl; auto. Qed.

Lemma main_cont_call_cont k : main_cont k -> call_cont k = Kstop.
Proof. induction k; simpl; intuition. Qed.

Lemma main_cont_is_call_cont k : main_cont k -> is_call_cont k -> k = Kstop.
Proof. destruct k; simpl; intuition. Qed.

Lemma above_find_label lbl :
  (forall s k s' k', above_main k -> find_label lbl s k = Some (s', k') ->
     above_main k') /\
  (forall ls k s' k', above_main k -> find_label_ls lbl ls k = Some (s', k') ->
     above_main k').
Proof.
  apply statement_labeled_statements_ind; simpl; intros; try discriminate.
  - destruct (find_label lbl s (Kseq s0 k)) eqn:E.
    + inv H2. eapply H; [| eassumption]. simpl; auto.
    + eauto.
  - destruct (find_label lbl s k) eqn:E.
    + inv H2. eauto.
    + eauto.
  - destruct (find_label lbl s (Kloop1 s s0 k)) eqn:E.
    + inv H2. eapply H; [| eassumption]. simpl; auto.
    + eapply H0; [| eassumption]. simpl; auto.
  - eapply H; [| eassumption]. simpl; auto.
  - destruct (ident_eq lbl l).
    + inv H1. auto.
    + eauto.
  - destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) k)) eqn:E.
    + inv H2. eapply H; [| eassumption]. simpl; auto.
    + eauto.
Qed.

Ltac in_main Hi :=
  destruct Hi as [(? & Hp & Hk & Hg) | Ha]; [subst; try discriminate | right; simpl; auto].

Lemma main_inv_step ge s t s' :
  step2 ge s t s' -> main_inv s -> main_inv s'.
Proof.
  intros Hs Hi. inv Hs; simpl in *.
  - (* assign *) in_main Hi. destruct Hg; [discriminate | left; auto].
  - (* set *) in_main Hi. destruct Hg; [discriminate | left; auto].
  - (* call *) in_main Hi. destruct Hg; [discriminate | right; left; auto].
  - (* builtin *) in_main Hi. destruct Hg; [discriminate | left; auto].
  - (* seq *) in_main Hi. apply andb_prop in Hp. destruct Hp.
    left. repeat split; auto.
    destruct Hg as [Hg | Hg]; auto. apply orb_prop in Hg. tauto.
  - (* skip seq *) in_main Hi. destruct Hk.
    left. repeat split; auto. destruct Hg; [discriminate | auto].
  - (* continue seq *) in_main Hi.
  - (* break seq *) in_main Hi.
  - (* if *) in_main Hi. apply andb_prop in Hp. destruct Hp.
    left. repeat split; auto.
    + destruct b; auto.
    + destruct Hg as [Hg | Hg]; auto. apply andb_prop in Hg.
      destruct Hg. destruct b; auto.
  - (* loop *) in_main Hi.
  - (* skip or continue loop1 *) in_main Hi. contradiction.
  - (* break loop1 *) in_main Hi.
  - (* skip loop2 *) in_main Hi. contradiction.
  - (* break loop2 *) in_main Hi.
  - (* return *) in_main Hi. apply above_call_cont; auto.
  - (* return a value *) destruct Hi as [(? & Hp & Hk & Hg) | Ha]; subst.
    + left. split; [apply main_cont_call_cont; auto |].
      rewrite main_int in *. eapply cast_to_int; eassumption.
    + right. apply above_call_cont; auto.
  - (* fall off the end *) in_main Hi.
    assert (k = Kstop) by (apply main_cont_is_call_cont; auto). subst.
    destruct Hg; [discriminate | contradiction].
  - (* switch *) in_main Hi.
  - (* skip or break switch *) in_main Hi. contradiction.
  - (* continue switch *) in_main Hi.
  - (* label *) in_main Hi.
  - (* goto *) destruct Hi as [(? & Hp & Hk & Hg) | Ha]; [discriminate |].
    right. eapply (proj1 (above_find_label lbl)); [| eassumption].
    apply above_call_cont; auto.
  - (* enter a function *) destruct Hi as [(E & ?) | Ha]; [| right; auto].
    inv E. left. repeat split; auto.
  - (* external call *) destruct Hi as [(E & ?) | Ha]; [discriminate | right; auto].
  - (* return to the caller *)
    destruct Hi as [(E & ?) | [(? & ? & ?) | Ha]]; [discriminate | | right; auto].
    subst. left. repeat split; auto.
Qed.

Lemma main_inv_star ge s t s' :
  star step2 ge s t s' -> main_inv s -> main_inv s'.
Proof.
  induction 1; auto. intros. eauto using main_inv_step.
Qed.

(** What the invariant is for. *)
Lemma main_returns_an_int ge args m t v m' :
  star step2 ge (Callstate (Internal fmain) args Kstop m) t
                (Returnstate v Kstop m') ->
  exists i, v = Vint i.
Proof.
  intros H. apply main_inv_star in H; [| left; auto].
  destruct H as [(_ & ?) | []]. assumption.
Qed.

End MAIN.

(** ** The join *)

Section JOIN.
Hypothesis Jsub : more_permission_same_call.
Hypothesis det : inline_calls_deterministic.
Context {CS : compspecs}.
Variables (prog : Clight.program) (V : mpred.varspecs) (G : mpred.funspecs)
  (m0 : mem) (fmain : function).
Hypothesis verified : @semax_prog NullExtension.Espec CS prog tt V G.
Hypothesis init : Genv.init_mem prog = Some m0.

Let ge := globalenv prog.

(** What VST's theorem concludes of a state: safe for any number of
    steps. *)
Definition vsafe (q : Core.CC_core) (m : mem) : Prop :=
  forall n,
    @dry_safeN _ _ _ unit (semax.genv_symb_injective)
      (Core.cl_core_sem ge) NullExtension.dryspec
      (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n tt q m.

(** VST's theorem, applied.  The other conditions it asks for are about
    the specification of external functions, and here there is none. *)
Lemma vst_safe :
  exists b q,
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
    Core.cl_initial_core ge (Vptr b Ptrofs.zero) nil = Some q /\
    vsafe q m0.
Proof.
  destruct (@whole_program_sequential_safety_ext CS NullExtension.Espec tt)
    with (dryspec := NullExtension.dryspec)
         (dessicate := fun (ef : external_function) (jm : juicy_mem)
            (x : ext_spec_type (@OK_spec NullExtension.Espec) ef) => x)
         (prog := prog) (V := V) (G := G) (m := m0)
    as (b & q & Hb & Hq & Hs); auto.
  - repeat intro. exact I.
  - intros ? ?. contradiction.
  - split; [| split].
    + intros. contradiction.
    + intros. contradiction.
    + intros. split; intros; hnf; auto.
  - hnf. intros. contradiction.
  - intros. hnf. auto.
  - exists b, q. repeat split; auto.
Qed.

(** A safe state has finished or can step. *)
Lemma vsafe_cases q m :
  vsafe q m ->
  (exists v, q = Core.Returnstate v Kstop) \/
  (exists q' m', Core.step ge q m q' m').
Proof.
  intros H. specialize (H 1%nat). inv H.
  - right. eauto.
  - contradiction.
  - left. simpl in H0. destruct q; simpl in H0; try congruence.
    destruct c; try congruence. eauto.
Qed.

(** Safety follows CompCert's steps. *)
Lemma vsafe_step q m t s' :
  vsafe q m -> step2 ge (Core.CC_core_to_CC_state q m) t s' ->
  exists q' m', s' = Core.CC_core_to_CC_state q' m' /\ vsafe q' m'.
Proof.
  intros H Hs.
  destruct (Core.CC_core_CC_state_4 s') as (q' & m' & ->).
  exists q', m'. split; auto. intros n. specialize (H (S n)). inv H.
  - pose proof (step2_after_core_step det _ _ _ _ _ _ _ H1 Hs) as E.
    apply Core.CC_core_to_CC_state_inj in E. inv E. assumption.
  - contradiction.
  - simpl in H0. destruct q; simpl in H0; try congruence.
    destruct c; try congruence. simpl in Hs. inv Hs.
Qed.

Lemma vsafe_star s t s' :
  star step2 ge s t s' ->
  forall q m, s = Core.CC_core_to_CC_state q m -> vsafe q m ->
  exists q' m', s' = Core.CC_core_to_CC_state q' m' /\ vsafe q' m'.
Proof.
  induction 1; intros q m E Hq; subst.
  - eauto.
  - destruct (vsafe_step _ _ _ _ Hq H) as (q1 & m1 & -> & H1). eauto.
Qed.

Hypothesis main_def :
  (prog_defmap prog) ! (prog_main prog) = Some (Gfun (Internal fmain)).
Hypothesis main_type : type_of_function fmain = Tfunction nil tint cc_default.
Hypothesis main_plain : plain (fn_body fmain) = true.
Hypothesis main_returns : returns (fn_body fmain) = true.

(** A program that VST has verified never goes wrong. *)
Theorem verified_program_never_goes_wrong : never_goes_wrong prog.
Proof.
  destruct vst_safe as (b & q & Hb & Hq & Hsafe).
  assert (Hf : Genv.find_funct_ptr ge b = Some (Internal fmain)).
  { apply Genv.find_def_symbol in main_def.
    destruct main_def as (b' & Hb' & Hd).
    unfold ge. simpl. rewrite Hb in Hb'. inv Hb'.
    apply Genv.find_funct_ptr_iff. exact Hd. }
  assert (Eq : q = Core.Callstate (Internal fmain) nil Kstop).
  { unfold Core.cl_initial_core in Hq.
    destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); [| congruence].
    rewrite Hf in Hq. congruence. }
  subst q.
  assert (main_int : fn_return fmain = tint).
  { unfold type_of_function in main_type. congruence. }
  intros beh Hbeh. inv Hbeh.
  - (* the program starts *)
    inv H. rewrite init in H1. inv H1.
    assert (b0 = b) by (unfold ge0 in *; congruence). subst b0.
    assert (f = Internal fmain).
    { change (Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal fmain)) in Hf.
      unfold ge0 in H3. rewrite Hf in H3. congruence. }
    subst f.
    destruct beh; simpl; auto.
    inv H0.
    match goal with
    | Hstar : Star _ _ _ ?s, Hno : Nostep _ ?s,
      Hnf : forall r, ~ Smallstep.final_state _ ?s r |- _ =>
        destruct (vsafe_star _ _ _ Hstar
                    (Core.Callstate (Internal fmain) nil Kstop) _ eq_refl Hsafe)
          as (q' & m' & -> & Hq');
        destruct (vsafe_cases _ _ Hq') as [(v & ->) | (q1 & m2 & Hstep)];
        [ destruct (main_returns_an_int fmain main_int main_plain main_returns
                      _ _ _ _ _ _ Hstar) as (i & ->);
          eelim Hnf; constructor
        | pose proof (Core.cl_corestep_not_at_external _ _ _ _ _ Hstep) as Hat;
          destruct (Core.cl_step_equiv _ _ _ _ _ Hat Hstep) as (t' & Ht');
          eelim Hno; exact Ht' ]
    end.
  - (* the program cannot fail to start *)
    eelim H. econstructor; eauto.
Qed.

End JOIN.
