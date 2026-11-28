(** * Removing arithmetic guards: the theorem

    [Guard.v] puts a test in front of each statement whose arithmetic the
    C standard leaves open for some operand values.  A test that succeeds
    jumps to a label that does not exist, which is stuck.  A VST proof of
    the guarded function therefore shows that no test succeeds, in the
    guarded function.

    This file proves what that says of the function without the tests.
    The result is [guards_removed], and it is the obligation recorded in
    the ledger as T0003.

    Let [p'] be [p] with guards, and let [p'] never go wrong.  Then:

    - every state an execution of [p] passes through is matched by a state
      an execution of [p'] passes through, with the same memory and the
      same variables.  So [p] takes the same steps as [p'], apart from the
      tests;
    - in each such state of [p], every test the transformation would put
      in front of the statement about to run evaluates to false.  So the
      operand values the tests look for do not arise in [p].

    The proof is a simulation.  [p'] follows each step of [p]: it first
    runs the tests in front of its statement, then takes the same step.
    That it gets past the tests is where its safety is used.  A test must
    evaluate, since [p'] cannot be stuck there, and it must come out
    false, since the jump would be stuck.

    What is not proven.  That [p] itself never goes wrong does not follow
    from this file.  That needs the other direction as well, that [p] can
    take each step [p'] takes, and it is not done.  For [adler32.c] it is
    not needed, since the functions without tests are verified directly.

    The proof needs CompCert only, not VST.  It uses excluded middle, to
    go from "never goes wrong" to "can always step or has finished", and
    CompCert's two axioms about external calls. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Values Memory
  Events Globalenvs Smallstep Behaviors Clight Maps Clightdefs Linking.
From Stdlib Require Import List Classical.
From fvzlib.proofs.lib Require Import Census Guard Executions.
Import ListNotations.

(** ** The transformation as a relation

    [guarded ret s' s]: [s'] is [s] with the tests in front of each
    statement that the transformation tests.  [ret] is the return type of
    the function, which the tests for a [return] depend on.  [plan_apply]
    ties the relation to the functions in [Guard.v] that compute the
    transformation. *)

Definition simple (s : statement) : Prop :=
  match s with
  | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _ | Sreturn _ => True
  | _ => False
  end.

Section RELATION.
Variable ret : type.

Inductive guarded : statement -> statement -> Prop :=
| guarded_simple s conds :
    simple s -> all_violations (scan_stmt ret s) = Some conds ->
    guarded (prefix conds s) s
| guarded_seq a b a' b' :
    guarded a' a -> guarded b' b -> guarded (Ssequence a' b') (Ssequence a b)
| guarded_if c a b a' b' conds :
    all_violations (scan_expr c) = Some conds ->
    guarded a' a -> guarded b' b ->
    guarded (prefix conds (Sifthenelse c a' b')) (Sifthenelse c a b)
| guarded_loop a b a' b' :
    guarded a' a -> guarded b' b -> guarded (Sloop a' b') (Sloop a b)
| guarded_switch e ls ls' conds :
    all_violations (scan_expr e) = Some conds ->
    guarded_cases ls' ls ->
    guarded (prefix conds (Sswitch e ls')) (Sswitch e ls)
| guarded_label l a a' :
    guarded a' a -> guarded (Slabel l a') (Slabel l a)
| guarded_skip : guarded Sskip Sskip
| guarded_break : guarded Sbreak Sbreak
| guarded_continue : guarded Scontinue Scontinue
| guarded_goto l : guarded (Sgoto l) (Sgoto l)
with guarded_cases : labeled_statements -> labeled_statements -> Prop :=
| guarded_nil : guarded_cases LSnil LSnil
| guarded_cons c s s' r r' :
    guarded s' s -> guarded_cases r' r ->
    guarded_cases (LScons c s' r') (LScons c s r).

Scheme guarded_ind2 := Minimality for guarded Sort Prop
  with guarded_cases_ind2 := Minimality for guarded_cases Sort Prop.
Combined Scheme guarded_both_ind from guarded_ind2, guarded_cases_ind2.

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_both_ind from statement_ind2, labeled_statements_ind2.

Lemma bind_some {A B} (x : option A) (f : A -> option B) y :
  bind x f = Some y -> exists a, x = Some a /\ f a = Some y.
Proof. destruct x; simpl; intros; [eauto | discriminate]. Qed.

Lemma plan_apply :
  (forall s p, plan_stmt ret s = Some p ->
     forall rest, exists s',
       apply_stmt s (p ++ rest) = (s', rest) /\ guarded s' s) /\
  (forall ls p, plan_cases ret ls = Some p ->
     forall rest, exists ls',
       apply_cases ls (p ++ rest) = (ls', rest) /\ guarded_cases ls' ls).
Proof.
  apply statement_both_ind; simpl; intros.
  all: repeat match goal with
       | H : bind _ _ = Some _ |- _ =>
           apply bind_some in H; destruct H as (? & ? & H)
       | H : Some _ = Some _ |- _ => inv H
       end.
  all: simpl; rewrite <- ?app_assoc.
  all: repeat match goal with
       | IH : forall p, plan_stmt ret ?s = Some p -> _,
         H : plan_stmt ret ?s = Some ?p |- context [apply_stmt ?s (?p ++ ?r)] =>
           destruct (IH _ H r) as (? & -> & ?); clear IH
       | IH : forall p, plan_cases ret ?s = Some p -> _,
         H : plan_cases ret ?s = Some ?p |- context [apply_cases ?s (?p ++ ?r)] =>
           destruct (IH _ H r) as (? & -> & ?); clear IH
       end.
  all: eexists; split; [reflexivity |].
  all: try (constructor; assumption).
  all: try (apply guarded_simple; simpl; auto).
Qed.

End RELATION.

(** ** Functions and programs *)

Record guarded_fun (f' f : function) : Prop := {
  gf_return : fn_return f' = fn_return f;
  gf_callconv : fn_callconv f' = fn_callconv f;
  gf_params : fn_params f' = fn_params f;
  gf_vars : fn_vars f' = fn_vars f;
  gf_temps : fn_temps f' = fn_temps f;
  gf_body : guarded (fn_return f) (fn_body f') (fn_body f)
}.

Lemma guard_function_guarded f f' :
  guard_function f = Some f' -> guarded_fun f' f.
Proof.
  unfold guard_function, guard_plan, apply_plan. intros H.
  apply bind_some in H. destruct H as (p & Hp & H). inv H.
  destruct (proj1 (plan_apply (fn_return f)) _ _ Hp []) as (s' & E & G).
  rewrite app_nil_r in E.
  constructor; simpl; auto. rewrite E. exact G.
Qed.

Inductive guarded_fundef : Clight.fundef -> Clight.fundef -> Prop :=
| guarded_internal f' f :
    guarded_fun f' f -> guarded_fundef (Internal f') (Internal f)
| guarded_external ef targs tres cc :
    guarded_fundef (External ef targs tres cc) (External ef targs tres cc).

Definition guard_fundef (fd : Clight.fundef) : option Clight.fundef :=
  match fd with
  | Internal f => bind (guard_function f) (fun f' => Some (Internal f'))
  | External _ _ _ _ => Some fd
  end.

Definition guard_globdef (d : ident * globdef Clight.fundef type)
  : option (ident * globdef Clight.fundef type) :=
  match d with
  | (id, Gfun fd) => bind (guard_fundef fd) (fun fd' => Some (id, Gfun fd'))
  | (id, Gvar v) => Some d
  end.

Fixpoint guard_globdefs (ds : list (ident * globdef Clight.fundef type))
  : option (list (ident * globdef Clight.fundef type)) :=
  match ds with
  | [] => Some []
  | d :: rest =>
      bind (guard_globdef d) (fun d' =>
      bind (guard_globdefs rest) (fun rest' => Some (d' :: rest')))
  end.

(** The program with every function guarded.  [None] if the
    transformation refuses some function. *)
Definition guard_program (p : Clight.program) : option Clight.program :=
  bind (guard_globdefs (prog_defs p)) (fun defs =>
    Some {| prog_defs := defs;
            prog_public := prog_public p;
            prog_main := prog_main p;
            prog_types := prog_types p;
            prog_comp_env := prog_comp_env p;
            prog_comp_env_eq := prog_comp_env_eq p |}).

Definition match_fundef (ctx : AST.program Clight.fundef type)
    (fd fd' : Clight.fundef) : Prop :=
  guarded_fundef fd' fd.

(** [p'] is [p] with guards added. *)
Record guarded_program (p' p : Clight.program) : Prop := {
  gp_defs : match_program_gen match_fundef eq (program_of_program p) p p';
  gp_cenv : prog_comp_env p' = prog_comp_env p
}.

Lemma guard_fundef_guarded fd fd' :
  guard_fundef fd = Some fd' -> guarded_fundef fd' fd.
Proof.
  destruct fd; simpl; intros H.
  - apply bind_some in H. destruct H as (f' & Hf & H). inv H.
    constructor. apply guard_function_guarded. assumption.
  - inv H. constructor.
Qed.

Lemma guard_program_guarded p p' :
  guard_program p = Some p' -> guarded_program p' p.
Proof.
  unfold guard_program. intros H.
  apply bind_some in H. destruct H as (defs & Hd & H). inv H.
  constructor; simpl; auto.
  split; [| split; reflexivity]. simpl.
  revert defs Hd. generalize (prog_defs p).
  induction l as [| d rest IH]; simpl; intros defs Hd.
  - inv Hd. constructor.
  - apply bind_some in Hd. destruct Hd as (d' & Hd' & Hd).
    apply bind_some in Hd. destruct Hd as (rest' & Hr & Hd). inv Hd.
    constructor; [| apply IH; assumption].
    destruct d as [id [fd | v]]; simpl in Hd'.
    + apply bind_some in Hd'. destruct Hd' as (fd' & Hf & Hd'). inv Hd'.
      split; [reflexivity |]. simpl.
      eapply match_globdef_fun; [apply linkorder_refl |].
      apply guard_fundef_guarded. assumption.
    + inv Hd'. split; [reflexivity |]. simpl.
      destruct v. constructor. constructor. reflexivity.
Qed.

(** ** Two global environments that differ only in function bodies *)

Section SAME_ENV.
Variables g1 g2 : genv.
Hypothesis Hc : genv_cenv g2 = genv_cenv g1.
Hypothesis Hs : forall id, Genv.find_symbol g2 id = Genv.find_symbol g1 id.

Lemma eval_same e le m :
  (forall a v, eval_expr g1 e le m a v -> eval_expr g2 e le m a v) /\
  (forall a b o bf, eval_lvalue g1 e le m a b o bf ->
     eval_lvalue g2 e le m a b o bf).
Proof.
  apply eval_expr_lvalue_ind; intros;
    try (econstructor; eauto; rewrite ?Hc, ?Hs; eauto; fail).
  - rewrite <- Hc. constructor.
  - rewrite <- Hc. constructor.
Qed.

Lemma eval_expr_same e le m a v :
  eval_expr g1 e le m a v -> eval_expr g2 e le m a v.
Proof. apply eval_same. Qed.

Lemma eval_lvalue_same e le m a b o bf :
  eval_lvalue g1 e le m a b o bf -> eval_lvalue g2 e le m a b o bf.
Proof. apply eval_same. Qed.

Lemma eval_exprlist_same e le m al tys vl :
  eval_exprlist g1 e le m al tys vl -> eval_exprlist g2 e le m al tys vl.
Proof. induction 1; econstructor; eauto using eval_expr_same. Qed.

Lemma assign_loc_same ty m b o bf v m' :
  assign_loc g1 ty m b o bf v m' -> assign_loc g2 ty m b o bf v m'.
Proof. intros H. rewrite Hc. exact H. Qed.

Lemma alloc_variables_same e m vars e' m' :
  alloc_variables g1 e m vars e' m' -> alloc_variables g2 e m vars e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite Hc. eassumption.
Qed.

Lemma blocks_of_env_same e : blocks_of_env g2 e = blocks_of_env g1 e.
Proof. unfold blocks_of_env, block_of_binding. rewrite Hc. reflexivity. Qed.
End SAME_ENV.

(** ** Continuations and states *)

(** The label a guard jumps to is not in the function, so the jump is
    stuck. *)
Definition fun_ok (f' : function) : Prop :=
  forall k, find_label _fvz_undefined (fn_body f') k = None.

Definition fundef_ok (fd' : Clight.fundef) : Prop :=
  match fd' with Internal f' => fun_ok f' | External _ _ _ _ => True end.

Inductive match_cont (ret : type) : cont -> cont -> Prop :=
| mc_stop : match_cont ret Kstop Kstop
| mc_seq s' s k' k :
    guarded ret s' s -> match_cont ret k' k ->
    match_cont ret (Kseq s' k') (Kseq s k)
| mc_loop1 a' a b' b k' k :
    guarded ret a' a -> guarded ret b' b -> match_cont ret k' k ->
    match_cont ret (Kloop1 a' b' k') (Kloop1 a b k)
| mc_loop2 a' a b' b k' k :
    guarded ret a' a -> guarded ret b' b -> match_cont ret k' k ->
    match_cont ret (Kloop2 a' b' k') (Kloop2 a b k)
| mc_switch k' k :
    match_cont ret k' k -> match_cont ret (Kswitch k') (Kswitch k)
| mc_call optid f' f e le k' k :
    guarded_fun f' f -> fun_ok f' -> match_cont (fn_return f) k' k ->
    match_cont ret (Kcall optid f' e le k') (Kcall optid f e le k).

Inductive match_states : state -> state -> Prop :=
| ms_state f' f s' s k' k e le m :
    guarded_fun f' f -> fun_ok f' ->
    guarded (fn_return f) s' s -> match_cont (fn_return f) k' k ->
    match_states (State f' s' k' e le m) (State f s k e le m)
| ms_call fd' fd args k' k m :
    guarded_fundef fd' fd -> fundef_ok fd' ->
    is_call_cont k -> match_cont Tvoid k' k ->
    match_states (Callstate fd' args k' m) (Callstate fd args k m)
| ms_return v k' k m :
    is_call_cont k -> match_cont Tvoid k' k ->
    match_states (Returnstate v k' m) (Returnstate v k m).

Lemma mc_call_cont ret k' k :
  match_cont ret k' k -> match_cont ret (call_cont k') (call_cont k).
Proof. induction 1; simpl; auto; econstructor; eauto. Qed.

Lemma mc_is_call_cont ret k' k :
  match_cont ret k' k -> is_call_cont k -> is_call_cont k'.
Proof. destruct 1; simpl; auto. Qed.

Lemma mc_any ret ret2 k' k :
  is_call_cont k -> match_cont ret k' k -> match_cont ret2 k' k.
Proof. intros C H. inv H; simpl in C; try contradiction; econstructor; eauto. Qed.

Lemma call_cont_is_call_cont k : is_call_cont (call_cont k).
Proof. induction k; simpl; auto. Qed.

Lemma guarded_seq_of_ls ret ls' ls :
  guarded_cases ret ls' ls ->
  guarded ret (seq_of_labeled_statement ls') (seq_of_labeled_statement ls).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma guarded_select_default ret ls' ls :
  guarded_cases ret ls' ls ->
  guarded_cases ret (select_switch_default ls') (select_switch_default ls).
Proof.
  induction 1; simpl; [constructor |].
  destruct c; auto. constructor; auto.
Qed.

Lemma guarded_select_case ret n ls' ls :
  guarded_cases ret ls' ls ->
  match select_switch_case n ls', select_switch_case n ls with
  | Some a', Some a => guarded_cases ret a' a
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1; simpl; auto.
  destruct c; auto. destruct (zeq z n); auto. constructor; auto.
Qed.

Lemma guarded_select ret n ls' ls :
  guarded_cases ret ls' ls ->
  guarded_cases ret (select_switch n ls') (select_switch n ls).
Proof.
  intros H. unfold select_switch.
  pose proof (guarded_select_case ret n _ _ H) as C.
  destruct (select_switch_case n ls'), (select_switch_case n ls);
    try contradiction; auto.
  apply guarded_select_default. assumption.
Qed.

(** Labels are found in the same places. *)
Lemma find_label_prefix lbl conds s k :
  find_label lbl (prefix conds s) k = find_label lbl s k.
Proof. induction conds; simpl; auto. Qed.

Definition found (ret : type) (x' x : option (statement * cont)) : Prop :=
  match x', x with
  | Some (t', kt'), Some (t, kt) => guarded ret t' t /\ match_cont ret kt' kt
  | None, None => True
  | _, _ => False
  end.

Lemma find_label_guarded ret lbl :
  (forall s' s, guarded ret s' s ->
     forall k' k, match_cont ret k' k ->
     found ret (find_label lbl s' k') (find_label lbl s k)) /\
  (forall ls' ls, guarded_cases ret ls' ls ->
     forall k' k, match_cont ret k' k ->
     found ret (find_label_ls lbl ls' k') (find_label_ls lbl ls k)).
Proof.
  apply guarded_both_ind; intros; rewrite ?find_label_prefix; simpl.
  - destruct s; simpl in *; try contradiction; exact I.
  - specialize (H0 (Kseq b' k') (Kseq b k)).
    specialize (H2 k' k H3).
    assert (C : match_cont ret (Kseq b' k') (Kseq b k)) by (constructor; auto).
    specialize (H0 C). unfold found in *.
    destruct (find_label lbl a' (Kseq b' k')) as [[] |],
             (find_label lbl a (Kseq b k)) as [[] |]; try contradiction; auto.
  - specialize (H1 k' k H4). specialize (H3 k' k H4). unfold found in *.
    destruct (find_label lbl a' k') as [[] |],
             (find_label lbl a k) as [[] |]; try contradiction; auto.
  - assert (C1 : match_cont ret (Kloop1 a' b' k') (Kloop1 a b k))
      by (constructor; auto).
    assert (C2 : match_cont ret (Kloop2 a' b' k') (Kloop2 a b k))
      by (constructor; auto).
    specialize (H0 _ _ C1). specialize (H2 _ _ C2). unfold found in *.
    destruct (find_label lbl a' (Kloop1 a' b' k')) as [[] |],
             (find_label lbl a (Kloop1 a b k)) as [[] |]; try contradiction; auto.
  - apply H1. constructor; auto.
  - destruct (ident_eq lbl l).
    + split; auto.
    + auto.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - assert (C : match_cont ret (Kseq (seq_of_labeled_statement r') k')
                              (Kseq (seq_of_labeled_statement r) k))
      by (constructor; auto using guarded_seq_of_ls).
    specialize (H0 _ _ C). specialize (H2 _ _ H3). unfold found in *.
    destruct (find_label lbl s' (Kseq (seq_of_labeled_statement r') k')) as [[] |],
             (find_label lbl s (Kseq (seq_of_labeled_statement r) k)) as [[] |];
      try contradiction; auto.
Qed.

(** ** The simulation *)

Section SIMULATION.
Variables p p' : Clight.program.
Hypothesis related : guarded_program p' p.
Hypothesis label_new :
  forall id fd', In (id, Gfun fd') (prog_defs p') -> fundef_ok fd'.

Let ge := globalenv p.
Let ge' := globalenv p'.
Let L := semantics2 p.
Let L' := semantics2 p'.

Lemma cenv_same : genv_cenv ge' = genv_cenv ge.
Proof. exact (gp_cenv _ _ related). Qed.

Lemma cenv_back : genv_cenv ge = genv_cenv ge'.
Proof. symmetry. exact cenv_same. Qed.

Lemma symbols_same id : Genv.find_symbol ge' id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_match (gp_defs _ _ related) id). Qed.

Lemma symbols_back id : Genv.find_symbol ge id = Genv.find_symbol ge' id.
Proof. symmetry. apply symbols_same. Qed.

Lemma senv_same : Senv.equiv ge ge'.
Proof. exact (Genv.senv_match (gp_defs _ _ related)). Qed.

Lemma type_of_guarded fd' fd :
  guarded_fundef fd' fd -> type_of_fundef fd' = type_of_fundef fd.
Proof.
  destruct 1 as [f' f [] |]; simpl; auto.
  unfold type_of_function. congruence.
Qed.

Lemma function_found v fd :
  Genv.find_funct ge v = Some fd ->
  exists fd', Genv.find_funct ge' v = Some fd' /\
              guarded_fundef fd' fd /\ fundef_ok fd'.
Proof.
  intros H.
  destruct (Genv.find_funct_match (gp_defs _ _ related) _ H)
    as (cu & fd' & H' & M & _).
  exists fd'. repeat split; auto.
  apply Genv.find_funct_inversion in H'. destruct H' as (id & Hin).
  eapply label_new. exact Hin.
Qed.

(** *** Getting past the tests

    The guarded program is safe, so each test can be evaluated, and it
    cannot come out true: the jump it would then make is stuck. *)
Definition test_fails (g : genv) (e : env) (le : temp_env) (m : mem)
    (c : expr) : Prop :=
  exists v, eval_expr g e le m c v /\ bool_val v (typeof c) m = Some false.

Lemma run_guards f' conds s k e le m :
  fun_ok f' ->
  safe L' (State f' (prefix conds s) k e le m) ->
  star step2 ge' (State f' (prefix conds s) k e le m) E0 (State f' s k e le m) /\
  Forall (test_fails ge' e le m) conds.
Proof.
  intros Hok. induction conds as [| c rest IH]; simpl; intros Hsafe.
  - split; [apply star_refl | constructor].
  - set (s1 := State f' (guard c) (Kseq (prefix rest s) k) e le m).
    assert (S1 : star step2 ge' (State f' (Ssequence (guard c) (prefix rest s)) k e le m)
                   E0 s1) by (apply star_one; constructor).
    pose proof (@star_safe L' _ _ S1 Hsafe) as Hs1.
    destruct (Hs1 _ (star_refl _ _ _)) as [(r & F) | (t & s2 & St)]; [inv F |].
    unfold s1, guard in St. inv St.
    match goal with
    | Hb : bool_val _ _ _ = Some ?b |- _ => destruct b
    end.
    + (* the test is true: the jump is stuck *)
      exfalso.
      assert (S2 : star step2 ge' s1 E0
                     (State f' (Sgoto _fvz_undefined) (Kseq (prefix rest s) k) e le m)).
      { apply star_one. unfold s1, guard.
        eapply (step_ifthenelse ge' (function_entry2 ge') f' c
                  (Sgoto _fvz_undefined) Sskip _ e le m _ true); eassumption. }
      pose proof (@star_safe L' _ _ S2 Hs1) as Hs2.
      destruct (Hs2 _ (star_refl _ _ _)) as [(r & F) | (t & s3 & St)]; [inv F |].
      inv St. rewrite Hok in *. discriminate.
    + assert (S2 : star step2 ge' s1 E0 (State f' (prefix rest s) k e le m)).
      { eapply star_two;
          [ unfold s1, guard;
            eapply (step_ifthenelse ge' (function_entry2 ge') f' c
                      (Sgoto _fvz_undefined) Sskip _ e le m _ false); eassumption
          | apply step_skip_seq | reflexivity ]. }
      pose proof (@star_safe L' _ _ S2 Hs1) as Hs2.
      destruct (IH Hs2) as (Hstar & Hall).
      split.
      * eapply star_trans; [exact S1 |
          eapply star_trans; [exact S2 | exact Hstar | reflexivity] | reflexivity].
      * constructor; [eexists; eauto | exact Hall].
Qed.

(** *** One step of the original, followed by the guarded program *)

Lemma eval_expr' e le m a v :
  eval_expr ge e le m a v -> eval_expr ge' e le m a v.
Proof. apply eval_expr_same; [exact cenv_same | exact symbols_same]. Qed.

Lemma eval_lvalue' e le m a b o bf :
  eval_lvalue ge e le m a b o bf -> eval_lvalue ge' e le m a b o bf.
Proof. apply eval_lvalue_same; [exact cenv_same | exact symbols_same]. Qed.

Lemma eval_exprlist' e le m al tys vl :
  eval_exprlist ge e le m al tys vl -> eval_exprlist ge' e le m al tys vl.
Proof. apply eval_exprlist_same; [exact cenv_same | exact symbols_same]. Qed.

Lemma assign_loc' ty m b o bf v m' :
  assign_loc ge ty m b o bf v m' -> assign_loc ge' ty m b o bf v m'.
Proof. apply assign_loc_same. exact cenv_same. Qed.

Lemma blocks_of_env' e : blocks_of_env ge' e = blocks_of_env ge e.
Proof. apply blocks_of_env_same. exact cenv_same. Qed.

Lemma function_entry' f' f vargs m e le m1 :
  guarded_fun f' f ->
  function_entry2 ge f vargs m e le m1 ->
  function_entry2 ge' f' vargs m e le m1.
Proof.
  intros [] H. inv H. constructor.
  - rewrite gf_vars0. assumption.
  - rewrite gf_params0. assumption.
  - rewrite gf_params0, gf_temps0. assumption.
  - rewrite gf_vars0. eapply alloc_variables_same; [exact cenv_same | eassumption].
  - rewrite gf_params0, gf_temps0. assumption.
Qed.

Lemma plus_after g a b c t :
  star step2 g a E0 b -> step2 g b t c -> plus step2 g a t c.
Proof. intros. eapply plus_right; eauto. Qed.

Create HintDb guard.
Local Hint Resolve eval_expr' eval_lvalue' eval_exprlist' assign_loc' : guard.

(** Run the tests in front of a statement, then take one more step. *)
Ltac after_guards :=
  match goal with
  | Hok : fun_ok _, Hsafe : safe _ _ |- _ =>
      destruct (run_guards _ _ _ _ _ _ _ Hok Hsafe) as (Hstar & _)
  end;
  eexists; split; [eapply plus_after; [eassumption |] |].

Ltac one_step := eexists; split; [apply plus_one |].

Ltac inv_guarded :=
  match goal with
  | H : guarded _ _ _ |- _ => inv H
  end;
  try match goal with H : simple _ |- _ => simpl in H; contradiction end.

Ltac inv_cont :=
  match goal with
  | H : match_cont _ _ (Kseq _ _) |- _ => inv H
  | H : match_cont _ _ (Kloop1 _ _ _) |- _ => inv H
  | H : match_cont _ _ (Kloop2 _ _ _) |- _ => inv H
  | H : match_cont _ _ (Kswitch _) |- _ => inv H
  | H : match_cont _ _ (Kcall _ _ _ _ _) |- _ => inv H
  end.

Ltac returned :=
  constructor;
  [ apply call_cont_is_call_cont
  | eapply mc_any; [apply call_cont_is_call_cont | apply mc_call_cont; eassumption] ].

Lemma lift_step s t s2 :
  step2 ge s t s2 ->
  forall s', match_states s' s -> safe L' s' ->
  exists s2', plus step2 ge' s' t s2' /\ match_states s2' s2.
Proof.
  intros Hs s' Hm Hsafe. inv Hs; inv Hm.
  - (* assign *) inv_guarded. after_guards.
    + eapply step_assign; eauto with guard.
    + constructor; auto. constructor.
  - (* set *) inv_guarded. after_guards.
    + eapply step_set; eauto with guard.
    + constructor; auto. constructor.
  - (* call *) inv_guarded.
    match goal with
    | H : Genv.find_funct _ _ = Some _ |- _ =>
        destruct (function_found _ _ H) as (fd' & F' & G' & O')
    end.
    after_guards.
    + eapply step_call; eauto with guard.
      rewrite (type_of_guarded _ _ G'). assumption.
    + constructor; auto; try exact I. econstructor; eauto.
  - (* builtin *) inv_guarded. after_guards.
    + eapply step_builtin; eauto with guard.
      eapply external_call_symbols_preserved; [apply senv_same | eassumption].
    + constructor; auto. constructor.
  - (* seq *) inv_guarded. one_step.
    + apply step_seq.
    + constructor; auto. constructor; auto.
  - (* skip seq *) inv_guarded. inv_cont. one_step.
    + apply step_skip_seq.
    + constructor; auto.
  - (* continue seq *) inv_guarded. inv_cont. one_step.
    + apply step_continue_seq.
    + constructor; auto. constructor.
  - (* break seq *) inv_guarded. inv_cont. one_step.
    + apply step_break_seq.
    + constructor; auto. constructor.
  - (* if *) inv_guarded. after_guards.
    + eapply step_ifthenelse; eauto with guard.
    + constructor; auto. destruct b; auto.
  - (* loop *) inv_guarded. one_step.
    + apply step_loop.
    + constructor; auto. constructor; auto.
  - (* skip or continue loop1 *)
    match goal with H : _ \/ _ |- _ => destruct H; subst end;
      inv_guarded; inv_cont; one_step;
      [ apply step_skip_or_continue_loop1; auto
      | constructor; auto; constructor; auto
      | apply step_skip_or_continue_loop1; auto
      | constructor; auto; constructor; auto ].
  - (* break loop1 *) inv_guarded. inv_cont. one_step.
    + apply step_break_loop1.
    + constructor; auto. constructor.
  - (* skip loop2 *) inv_guarded. inv_cont. one_step.
    + apply step_skip_loop2.
    + constructor; auto. constructor; auto.
  - (* break loop2 *) inv_guarded. inv_cont. one_step.
    + apply step_break_loop2.
    + constructor; auto. constructor.
  - (* return *) inv_guarded. after_guards.
    + eapply step_return_0. rewrite blocks_of_env'. eassumption.
    + returned.
  - (* return a value *) inv_guarded. after_guards.
    + eapply step_return_1; eauto with guard.
      * erewrite gf_return by eassumption. eassumption.
      * rewrite blocks_of_env'. eassumption.
    + returned.
  - (* fall off the end *) inv_guarded. one_step.
    + apply step_skip_call.
      * eapply mc_is_call_cont; eauto.
      * rewrite blocks_of_env'. eassumption.
    + constructor; auto. eapply mc_any; eauto.
  - (* switch *) inv_guarded. after_guards.
    + eapply step_switch; eauto with guard.
    + constructor; auto.
      * apply guarded_seq_of_ls. apply guarded_select. assumption.
      * constructor. assumption.
  - (* skip or break switch *)
    match goal with H : _ \/ _ |- _ => destruct H; subst end;
      inv_guarded; inv_cont; one_step;
      [ apply step_skip_break_switch; auto
      | constructor; auto; constructor
      | apply step_skip_break_switch; auto
      | constructor; auto; constructor ].
  - (* continue switch *) inv_guarded. inv_cont. one_step.
    + apply step_continue_switch.
    + constructor; auto. constructor.
  - (* label *) inv_guarded. one_step.
    + apply step_label.
    + constructor; auto.
  - (* goto *) inv_guarded.
    match goal with
    | Hf : guarded_fun ?f' ?f, Hk : match_cont _ ?k' ?k,
      Hl : find_label ?lbl (fn_body ?f) (call_cont ?k) = Some _ |- _ =>
        pose proof (proj1 (find_label_guarded (fn_return f) lbl) _ _
                      (gf_body _ _ Hf) _ _ (mc_call_cont _ _ _ Hk)) as F;
        rewrite Hl in F;
        destruct (find_label lbl (fn_body f') (call_cont k')) as [[t' kt'] |] eqn:E;
          [destruct F | contradiction]
    end.
    one_step.
    + eapply step_goto. eassumption.
    + constructor; auto.
  - (* enter a function *)
    match goal with H : guarded_fundef _ (Internal _) |- _ => inv H end.
    one_step.
    + apply step_internal_function. eapply function_entry'; eauto.
    + constructor; auto.
      * apply gf_body. assumption.
      * eapply mc_any; eauto.
  - (* external call *)
    match goal with H : guarded_fundef _ (External _ _ _ _) |- _ => inv H end.
    one_step.
    + apply step_external_function.
      eapply external_call_symbols_preserved; [apply senv_same | eassumption].
    + constructor; auto.
  - (* return to the caller *) inv_cont. one_step.
    + apply step_returnstate.
    + constructor; auto. constructor.
Qed.

(** *** Whole executions *)

Lemma lift_initial s :
  initial_state p s -> exists s', initial_state p' s' /\ match_states s' s.
Proof.
  intros H. inv H.
  match goal with
  | Hf : Genv.find_funct_ptr _ _ = Some _ |- _ =>
      destruct (Genv.find_funct_ptr_match (gp_defs _ _ related) _ Hf)
        as (cu & fd' & F' & M & _)
  end.
  exists (Callstate fd' nil Kstop m0). split.
  - econstructor.
    + eapply (Genv.init_mem_match (gp_defs _ _ related)). eassumption.
    + replace (prog_main p') with (prog_main p)
        by (symmetry; exact (proj1 (proj2 (gp_defs _ _ related)))).
      rewrite (Genv.find_symbol_match (gp_defs _ _ related)). eassumption.
    + exact F'.
    + rewrite (type_of_guarded _ _ M). assumption.
  - constructor; auto.
    + apply Genv.find_funct_ptr_inversion in F'. destruct F' as (id & Hin).
      eapply label_new. exact Hin.
    + exact I.
    + constructor.
Qed.

Hypothesis guarded_safe : never_goes_wrong p'.

Lemma lift_star s t s1 :
  Star L s t s1 ->
  forall s', reachable p' s' -> match_states s' s ->
  exists s1', reachable p' s1' /\ match_states s1' s1.
Proof.
  induction 1; intros s' R M.
  - eauto.
  - destruct (lift_step _ _ _ H _ M (reachable_safe _ _ guarded_safe R))
      as (s2' & P & M2).
    eapply IHstar; [| exact M2].
    eapply reachable_step; [exact R | apply plus_star; exact P].
Qed.

(** Every state the original program reaches, the guarded program
    reaches too, apart from the tests. *)
Theorem lift_reachable s :
  reachable p s -> exists s', reachable p' s' /\ match_states s' s.
Proof.
  intros (s0 & t & I & S).
  destruct (lift_initial _ I) as (s0' & I' & M).
  eapply lift_star; [exact S | | exact M].
  exists s0', E0. split; [exact I' | apply star_refl].
Qed.

(** *** No test's condition ever holds *)

(** The tests the transformation puts in front of a statement. *)
Definition tests (ret : type) (s : statement) : option (list expr) :=
  match s with
  | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _ | Sreturn _ =>
      all_violations (scan_stmt ret s)
  | Sifthenelse c _ _ => all_violations (scan_expr c)
  | Sswitch e _ => all_violations (scan_expr e)
  | _ => Some []
  end.

(** In this state, every test for the statement about to run comes out
    false. *)
Definition no_violation (g : genv) (s : state) : Prop :=
  match s with
  | State f st k e le m =>
      forall conds, tests (fn_return f) st = Some conds ->
      Forall (test_fails g e le m) conds
  | _ => True
  end.

Lemma test_fails_back e le m c :
  test_fails ge' e le m c -> test_fails ge e le m c.
Proof.
  intros (v & E & B). exists v. split; auto.
  eapply eval_expr_same; [exact cenv_back | exact symbols_back | exact E].
Qed.

Theorem guards_never_fire s : reachable p s -> no_violation ge s.
Proof.
  intros R. destruct (lift_reachable _ R) as (s' & R' & M).
  pose proof (reachable_safe _ _ guarded_safe R') as Hsafe.
  destruct s; simpl; auto. intros conds T. inv M.
  match goal with
  | Hg : guarded _ ?sg _, Hok : fun_ok _ |- _ =>
      assert (through : forall cs st,
                sg = prefix cs st -> tests (fn_return f) s = Some cs ->
                Forall (test_fails ge e le m) conds);
      [ intros cs st E T'; subst sg; rewrite T in T'; inv T';
        destruct (run_guards _ _ _ _ _ _ _ Hok Hsafe) as (_ & F);
        eapply Forall_impl; [| exact F]; intros; apply test_fails_back;
        assumption
      | inv Hg ]
  end.
  all: try (simpl in T; inv T; constructor).
  - eapply through; [reflexivity |].
    destruct s; simpl in *; try contradiction; assumption.
  - eapply through; [reflexivity |]. assumption.
  - eapply through; [reflexivity |]. assumption.
Qed.

End SIMULATION.

(** ** The condition on labels, as a check that can be computed *)

Fixpoint has_label (l : label) (s : statement) : bool :=
  match s with
  | Ssequence a b | Sifthenelse _ a b | Sloop a b =>
      has_label l a || has_label l b
  | Sswitch _ cases => has_label_cases l cases
  | Slabel l' a => (if ident_eq l l' then true else false) || has_label l a
  | _ => false
  end
with has_label_cases (l : label) (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => false
  | LScons _ s rest => has_label l s || has_label_cases l rest
  end.

Lemma no_label_no_find l :
  (forall s, has_label l s = false -> forall k, find_label l s k = None) /\
  (forall ls, has_label_cases l ls = false ->
     forall k, find_label_ls l ls k = None).
Proof.
  apply statement_both_ind; simpl; intros; auto.
  all: repeat match goal with
       | H : _ || _ = false |- _ => apply orb_false_elim in H; destruct H
       end.
  - rewrite H by auto. auto.
  - rewrite H by auto. auto.
  - rewrite H by auto. auto.
  - destruct (ident_eq l l0); [discriminate | auto].
  - rewrite H by auto. auto.
Qed.

Definition labels_new (p' : Clight.program) : bool :=
  forallb (fun d : ident * globdef Clight.fundef type =>
             match snd d with
             | Gfun (Internal f) => negb (has_label _fvz_undefined (fn_body f))
             | _ => true
             end) (prog_defs p').

Lemma labels_new_ok p' :
  labels_new p' = true ->
  forall id fd', In (id, Gfun fd') (prog_defs p') -> fundef_ok fd'.
Proof.
  unfold labels_new. intros H id fd' Hin.
  rewrite forallb_forall in H. specialize (H _ Hin). simpl in H.
  destruct fd'; simpl; auto.
  intros k. apply (proj1 (no_label_no_find _fvz_undefined)).
  destruct (has_label _fvz_undefined (fn_body f)); [discriminate | reflexivity].
Qed.

(** ** The result

    [p'] is [p] with guards, [p'] names the guards' label nowhere else,
    and [p'] never goes wrong.  Then whatever state [p] reaches, [p']
    reaches the matching one, and in that state of [p] every test for the
    statement about to run comes out false. *)
Theorem guards_removed p p' :
  guard_program p = Some p' ->
  labels_new p' = true ->
  never_goes_wrong p' ->
  forall s, reachable p s ->
    (exists s', reachable p' s' /\ match_states s' s) /\
    no_violation (globalenv p) s.
Proof.
  intros G Lb N s R.
  pose proof (guard_program_guarded _ _ G) as Rel.
  pose proof (labels_new_ok _ Lb) as Ok.
  split.
  - eapply lift_reachable; eauto.
  - eapply guards_never_fire; eauto.
Qed.
