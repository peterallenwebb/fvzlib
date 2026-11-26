(** * Bounded ticks bound the steps: the proof

    Proves [bounded_ticks_bound_steps] of [TickStatements.v].

    The argument uses a potential, a number assigned to each state.

    - Every step lowers the potential by at least one, apart from two kinds
      of step: entering a loop body and entering a function.  Those raise
      it by less than the size bound [K].
    - Each of those two steps is followed at once by a tick.  Until the
      tick is spent, no other such step can happen.

    So each rise is paid for by one spent tick, with at most one rise still
    unpaid at any moment.  The number of steps is then at most the
    starting potential plus [K] for each tick spent, plus [K] once.

    No part of the argument looks at memory or at the values computed.  It
    holds whatever the counter contains. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Values Memory
  Events Globalenvs Smallstep Clight Clightdefs.
From Stdlib Require Import List Lia.
Require Import Ticks TickStatements.
Import ListNotations.
Local Open Scope nat_scope.

Scheme stmt_ind2 := Induction for statement Sort Prop
  with cases_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme stmt_cases_ind from stmt_ind2, cases_ind2.

(** ** The potential

    [weight] is [size], except that a loop weighs 1.  Its body is paid for
    when it is entered. *)
Fixpoint weight (s : statement) : nat :=
  match s with
  | Sskip | Sbreak | Scontinue => 1
  | Sassign _ _ | Sset _ _ | Sbuiltin _ _ _ _ | Sreturn _ | Sgoto _ => 2
  | Scall _ _ _ => 6
  | Ssequence a b => weight a + weight b + 2
  | Sifthenelse _ a b => weight a + weight b + 1
  | Sloop _ _ => 1
  | Sswitch _ cases => weight_cases cases + 2
  | Slabel _ a => weight a + 1
  end
with weight_cases (cases : labeled_statements) : nat :=
  match cases with
  | LSnil => 1
  | LScons _ s rest => weight s + weight_cases rest + 2
  end.

Fixpoint cont_potential (k : cont) : nat :=
  match k with
  | Kstop => 0
  | Kseq s k => weight s + 1 + cont_potential k
  | Kloop1 _ b k => weight b + 4 + cont_potential k
  | Kloop2 _ _ k => 3 + cont_potential k
  | Kswitch k => 1 + cont_potential k
  | Kcall _ _ _ _ k => 2 + cont_potential k
  end.

Definition potential (s : state) : nat :=
  match s with
  | State _ st k _ _ _ => weight st + cont_potential k
  | Callstate _ _ k _ => 2 + cont_potential k
  | Returnstate _ k _ => cont_potential k
  end.

Lemma weight_le_size :
  (forall s, weight s <= size s) /\
  (forall cases, weight_cases cases <= size_cases cases).
Proof. apply stmt_cases_ind; simpl; intros; lia. Qed.

Lemma size_pos s : 1 <= size s.
Proof. destruct s; simpl; lia. Qed.

Lemma cont_potential_call_cont k :
  cont_potential (call_cont k) <= cont_potential k.
Proof. induction k; simpl; lia. Qed.

(** ** A switch continues with a tail of its cases *)

Inductive tail_of : labeled_statements -> labeled_statements -> Prop :=
| tail_same cases : tail_of cases cases
| tail_next cases c s rest : tail_of cases rest -> tail_of cases (LScons c s rest).

Lemma select_switch_default_tail cases :
  tail_of (select_switch_default cases) cases.
Proof.
  induction cases as [|c s rest IH]; simpl.
  - constructor.
  - destruct c; [constructor; exact IH | constructor].
Qed.

Lemma select_switch_case_tail n cases found :
  select_switch_case n cases = Some found -> tail_of found cases.
Proof.
  induction cases as [|c s rest IH]; simpl; intros H.
  - discriminate.
  - destruct c as [c|].
    + destruct (zeq c n).
      * inversion H; constructor.
      * constructor; auto.
    + constructor; auto.
Qed.

Lemma select_switch_tail n cases : tail_of (select_switch n cases) cases.
Proof.
  unfold select_switch.
  destruct (select_switch_case n cases) eqn:E.
  - eapply select_switch_case_tail; eauto.
  - apply select_switch_default_tail.
Qed.

Lemma tail_weight found cases :
  tail_of found cases -> weight_cases found <= weight_cases cases.
Proof. induction 1; simpl; lia. Qed.

Lemma tail_size found cases :
  tail_of found cases -> size_cases found <= size_cases cases.
Proof. induction 1; simpl; lia. Qed.

Lemma tail_ticked found cases :
  tail_of found cases -> ticked_cases cases -> ticked_cases found.
Proof. induction 1; simpl; intuition. Qed.

Lemma weight_seq_of cases :
  weight (seq_of_labeled_statement cases) = weight_cases cases.
Proof. induction cases; simpl; lia. Qed.

Lemma size_seq_of cases :
  size (seq_of_labeled_statement cases) = size_cases cases.
Proof. induction cases; simpl; lia. Qed.

Lemma ticked_seq_of cases :
  ticked_cases cases -> ticked (seq_of_labeled_statement cases).
Proof. induction cases; simpl; intuition. Qed.

(** ** The jump a tick makes is stuck *)

Lemma ticked_tick : ticked tick.
Proof. simpl. auto. Qed.

Lemma find_label_exhausted :
  (forall s k, ticked s -> find_label _fvz_exhausted s k = None) /\
  (forall cases k, ticked_cases cases ->
                   find_label_ls _fvz_exhausted cases k = None).
Proof.
  apply stmt_cases_ind; simpl; intros; auto.
  - (* sequence *)
    destruct H1. rewrite H by assumption. auto.
  - (* if *)
    destruct H1. rewrite H by assumption. auto.
  - (* loop *)
    destruct H1 as [Ha Hb].
    rewrite H; [auto|].
    destruct s; try contradiction. destruct Ha as [-> Ha].
    simpl. split; [exact ticked_tick | exact Ha].
  - (* label *)
    destruct H0 as [Hl Hs].
    destruct (ident_eq _fvz_exhausted l); [congruence | auto].
  - (* a case of a switch *)
    destruct H1. rewrite H by assumption. auto.
Qed.

Lemma instrumented_no_exhausted f k :
  instrumented f -> find_label _fvz_exhausted (fn_body f) k = None.
Proof.
  intros (body & -> & Hbody).
  apply (proj1 find_label_exhausted). simpl.
  split; [exact ticked_tick | exact Hbody].
Qed.

(** ** The steps of a tick, up to the one that spends it *)

Inductive in_tick : state -> Prop :=
| in_tick_1 f a k e le m :
    in_tick (State f (Ssequence tick a) k e le m)
| in_tick_2 f a k e le m :
    in_tick (State f tick (Kseq a k) e le m)
| in_tick_3 f a k e le m :
    in_tick (State f tick_load
               (Kseq (Ssequence tick_test tick_spend) (Kseq a k)) e le m)
| in_tick_4 f a k e le m :
    in_tick (State f Sskip
               (Kseq (Ssequence tick_test tick_spend) (Kseq a k)) e le m)
| in_tick_5 f a k e le m :
    in_tick (State f (Ssequence tick_test tick_spend) (Kseq a k) e le m)
| in_tick_6 f k e le m :
    in_tick (State f tick_test (Kseq tick_spend k) e le m)
| in_tick_7 f k e le m :
    in_tick (State f Sskip (Kseq tick_spend k) e le m)
| in_tick_stuck f k e le m :
    in_tick (State f (Sgoto _fvz_exhausted) (Kseq tick_spend k) e le m)
| in_tick_8 f k e le m :
    in_tick (State f tick_spend k e le m).

Section BOUND.

Variable ge : genv.
Variable entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable K : nat.

Hypothesis functions_ok :
  forall b f, Genv.find_funct_ptr ge b = Some (Internal f) ->
              instrumented f /\ size (fn_body f) <= K.

(** ** What holds of every state of an execution *)

Definition ok_function (f : function) : Prop :=
  instrumented f /\ size (fn_body f) <= K.

Definition ok_statement (s : statement) : Prop :=
  ticked s /\ size s <= K.

Fixpoint ok_cont (k : cont) : Prop :=
  match k with
  | Kstop => True
  | Kseq s k => ok_statement s /\ ok_cont k
  | Kloop1 a b k | Kloop2 a b k => ok_statement (Sloop a b) /\ ok_cont k
  | Kswitch k => ok_cont k
  | Kcall _ f _ _ k => ok_function f /\ ok_cont k
  end.

Definition ok_state (s : state) : Prop :=
  match s with
  | State f st k _ _ _ => ok_function f /\ ok_statement st /\ ok_cont k
  | Callstate fd _ k _ =>
      (forall f, fd = Internal f -> ok_function f) /\ ok_cont k
  | Returnstate _ k _ => ok_cont k
  end.

Lemma ok_call_cont k : ok_cont k -> ok_cont (call_cont k).
Proof. induction k; simpl; intuition. Qed.

Lemma ok_function_one f : ok_function f -> 1 <= K.
Proof. intros [_ H]. pose proof (size_pos (fn_body f)). lia. Qed.

Lemma ok_found vf fd :
  Genv.find_funct ge vf = Some fd -> forall f, fd = Internal f -> ok_function f.
Proof.
  intros H f ->.
  destruct (Genv.find_funct_inv _ _ H) as [b ->].
  rewrite Genv.find_funct_find_funct_ptr in H.
  exact (functions_ok _ _ H).
Qed.

(* Take apart what is known of a state that is running a statement. *)
Ltac state_hyps Hok :=
  let Hf := fresh "Hf" in
  destruct Hok as (Hf & [Ht Hsz] & Hk);
  pose proof (ok_function_one _ Hf) as HK1;
  destruct Hf as [Hi Hfs];
  unfold ok_statement in *; simpl in Ht, Hsz, Hk.

(* Show that the next state is still in order. *)
Ltac ok :=
  simpl; unfold ok_function, ok_statement; simpl;
  repeat split; auto; simpl; try lia.

(** ** One step

    It keeps [ok_state].  It lowers the potential, or else it enters a
    loop body or a function, raises the potential by less than [K], and
    lands at the start of a tick. *)
Lemma step_potential s t s1 :
  ok_state s -> step ge entry s t s1 ->
  ok_state s1 /\
  (potential s1 + 1 <= potential s \/
   (in_tick s1 /\ potential s1 + 1 <= potential s + K)).
Proof.
  intros Hok Hstep.
  inversion Hstep; subst; simpl in Hok.
  - (* assign *)
    state_hyps Hok. split; [ok | left; simpl; lia].
  - (* set *)
    state_hyps Hok. split; [ok | left; simpl; lia].
  - (* call *)
    state_hyps Hok.
    split; [split; [eapply ok_found; eauto | ok] | left; simpl; lia].
  - (* builtin *)
    state_hyps Hok. split; [ok | left; simpl; lia].
  - (* sequence *)
    state_hyps Hok. destruct Ht. split; [ok | left; simpl; lia].
  - (* skip, then the next statement *)
    state_hyps Hok. destruct Hk as [[? ?] ?]. split; [ok | left; simpl; lia].
  - (* continue, leaving a sequence *)
    state_hyps Hok. destruct Hk as [_ Hk]. split; [ok | left; simpl; lia].
  - (* break, leaving a sequence *)
    state_hyps Hok. destruct Hk as [_ Hk]. split; [ok | left; simpl; lia].
  - (* if *)
    state_hyps Hok. destruct Ht.
    destruct b; (split; [ok | left; simpl; lia]).
  - (* entering a loop body *)
    state_hyps Hok. destruct Ht as [Ha Hb].
    destruct s0; try contradiction. destruct Ha as [-> Ha].
    pose proof (proj1 weight_le_size s0_2) as Wa.
    pose proof (proj1 weight_le_size s2) as Wb.
    simpl in Hsz.
    split; [ok | right; split; [constructor | simpl; lia]].
  - (* end of a loop body *)
    state_hyps Hok. destruct Hk as [[[Ha Hb] Hsz2] Hk].
    split; [ok |].
    left. match goal with H : _ \/ _ |- _ => destruct H; subst end; simpl; lia.
  - (* break out of a loop body *)
    state_hyps Hok. destruct Hk as [[_ Hsz2] Hk].
    split; [ok | left; simpl; lia].
  - (* back to the top of the loop *)
    state_hyps Hok. destruct Hk as [[[Ha Hb] Hsz2] Hk].
    split; [ok | left; simpl; lia].
  - (* break out of the second part of a loop *)
    state_hyps Hok. destruct Hk as [[_ Hsz2] Hk].
    split; [ok | left; simpl; lia].
  - (* return *)
    state_hyps Hok.
    split; [apply ok_call_cont; auto |].
    left. simpl. pose proof (cont_potential_call_cont k). lia.
  - (* return with a value *)
    state_hyps Hok.
    split; [apply ok_call_cont; auto |].
    left. simpl. pose proof (cont_potential_call_cont k). lia.
  - (* falling off the end of a function *)
    state_hyps Hok. split; [exact Hk | left; simpl; lia].
  - (* switch *)
    state_hyps Hok.
    pose proof (select_switch_tail n sl) as T.
    pose proof (tail_size _ _ T). pose proof (tail_weight _ _ T).
    split.
    + ok.
      * apply ticked_seq_of. eapply tail_ticked; eauto.
      * rewrite size_seq_of. lia.
    + left. simpl. rewrite weight_seq_of. lia.
  - (* leaving a switch *)
    state_hyps Hok.
    split; [ok |].
    left. match goal with H : _ \/ _ |- _ => destruct H; subst end; simpl; lia.
  - (* continue, leaving a switch *)
    state_hyps Hok. split; [ok | left; simpl; lia].
  - (* label *)
    state_hyps Hok. destruct Ht. split; [ok | left; simpl; lia].
  - (* goto: impossible *)
    state_hyps Hok. subst lbl.
    match goal with H : find_label _ _ _ = Some _ |- _ =>
      rewrite (instrumented_no_exhausted f _ Hi) in H; discriminate
    end.
  - (* entering a function *)
    destruct Hok as (Hf & Hk).
    destruct (Hf f eq_refl) as [Hi Hsz]. pose proof Hi as (body & Hbody & Ht).
    pose proof (proj1 weight_le_size (fn_body f)) as W.
    split.
    + ok. rewrite Hbody. simpl. auto.
    + right. split; [rewrite Hbody; constructor | simpl; lia].
  - (* an external function *)
    destruct Hok as (_ & Hk). split; [exact Hk | left; simpl; lia].
  - (* back in the caller *)
    destruct Hok as (Hf & Hk). pose proof (ok_function_one _ Hf).
    destruct Hf. split; [ok | left; simpl; lia].
Qed.

(** ** One step inside a tick

    It lowers the potential, and it stays inside the tick unless it is the
    step that spends it. *)
Lemma step_in_tick s t s1 :
  ok_state s -> in_tick s -> step ge entry s t s1 ->
  potential s1 + 1 <= potential s /\ (in_tick s1 \/ spending s).
Proof.
  intros Hok Hin Hstep.
  destruct Hin;
    unfold tick, tick_load, tick_test, tick_spend in Hstep;
    inversion Hstep; subst;
    try match goal with H : is_call_cont (Kseq _ _) |- _ => contradiction end;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  - (* tick; a *)
    split; [simpl; lia | left; apply in_tick_2].
  - (* tick *)
    split; [simpl; lia | left; apply in_tick_3].
  - (* the load *)
    split; [simpl; lia | left; apply in_tick_4].
  - (* after the load *)
    split; [simpl; lia | left; apply in_tick_5].
  - (* test; spend *)
    split; [simpl; lia | left; apply in_tick_6].
  - (* the test *)
    split; [destruct b; simpl; lia |].
    left. destruct b; [apply in_tick_stuck | apply in_tick_7].
  - (* after the test *)
    split; [simpl; lia | left; apply in_tick_8].
  - (* the counter was zero: stuck *)
    destruct Hok as ([Hi _] & _).
    match goal with H : find_label _ _ _ = Some _ |- _ =>
      rewrite (instrumented_no_exhausted f _ Hi) in H; discriminate
    end.
  - (* the spend *)
    split; [simpl; lia | right; do 5 eexists; reflexivity].
Qed.

(** ** Many steps *)

Lemma run_bound s n c s' :
  run ge entry s n c s' -> ok_state s ->
  n <= potential s + K * (c + 1) /\
  (in_tick s -> n <= potential s + K * c).
Proof.
  induction 1 as [s | s t s1 n c s' Hsp Hstep Hrun IH
                    | s t s1 n c s' Hsp Hstep Hrun IH]; intros Hok.
  - split; intros; lia.
  - (* a step that spends a tick *)
    destruct (step_potential _ _ _ Hok Hstep) as [Hok1 Hpot].
    destruct (IH Hok1) as [IH0 IH1].
    split.
    + destruct Hpot as [Hd | [Hin Hup]].
      * nia.
      * specialize (IH1 Hin). nia.
    + intros Hin.
      destruct (step_in_tick _ _ _ Hok Hin Hstep) as [Hd _]. nia.
  - (* any other step *)
    destruct (step_potential _ _ _ Hok Hstep) as [Hok1 Hpot].
    destruct (IH Hok1) as [IH0 IH1].
    split.
    + destruct Hpot as [Hd | [Hin Hup]].
      * nia.
      * specialize (IH1 Hin). nia.
    + intros Hin.
      destruct (step_in_tick _ _ _ Hok Hin Hstep) as [Hd [Hin1 | Hs]].
      * specialize (IH1 Hin1). nia.
      * contradiction.
Qed.

End BOUND.

(** ** The theorem *)

Theorem bounded_ticks_bound_steps_holds : bounded_ticks_bound_steps.
Proof.
  intros ge entry K Hfun b fd args m s n c Hfd Hrun.
  assert (Hok : ok_state K (Callstate fd args Kstop m)).
  { simpl. split; [|exact I]. intros f ->. exact (Hfun _ _ Hfd). }
  destruct (run_bound ge entry K Hfun _ _ _ _ Hrun Hok) as [H _].
  simpl in H. lia.
Qed.

(** ** The instrumentation produces instrumented functions

    [add_ticks] gives a [ticked] statement when the statement it is given
    has no jump and no label.  That is the case for every function this
    project instruments: a function with a jump first has it removed. *)
Fixpoint plain (s : statement) : bool :=
  match s with
  | Sgoto _ | Slabel _ _ => false
  | Ssequence a b => plain a && plain b
  | Sifthenelse _ a b => plain a && plain b
  | Sloop a b => plain a && plain b
  | Sswitch _ cases => plain_cases cases
  | _ => true
  end
with plain_cases (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => true
  | LScons _ s rest => plain s && plain_cases rest
  end.

Lemma add_ticks_ticked :
  (forall s, plain s = true -> ticked (add_ticks s)) /\
  (forall cases, plain_cases cases = true ->
                 ticked_cases (add_ticks_cases cases)).
Proof.
  apply stmt_cases_ind; simpl; intros; auto; try discriminate;
    try (apply andb_prop in H1; destruct H1; auto).
Qed.

Theorem instrument_function_instrumented f :
  plain (fn_body f) = true -> instrumented (instrument_function f).
Proof.
  intros H. exists (add_ticks (fn_body f)).
  split; [reflexivity | apply add_ticks_ticked; exact H].
Qed.
