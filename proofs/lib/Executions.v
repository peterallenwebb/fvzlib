(** * Statements about executions

    The terms in which the project states what a program does when it
    runs.  They are CompCert's.  This file contains two definitions and
    one lemma, and needs CompCert only.

    The semantics is [Clight.semantics2], in which parameters are
    temporaries.  It is the one clightgen's output is written for, and the
    one VST's soundness theorem speaks of. *)

From compcert Require Import Coqlib Events Globalenvs Smallstep Behaviors
  Clight.
From Stdlib Require Import Classical.

(** No behavior of the program is a wrong one: it does not get stuck, and
    it does not fail to start.  This is the premise of CompCert's theorem
    about the code it compiles. *)
Definition never_goes_wrong (p : Clight.program) : Prop :=
  forall beh, program_behaves (Clight.semantics2 p) beh -> not_wrong beh.

(** A state some execution of the program passes through. *)
Definition reachable (p : Clight.program) (s : state) : Prop :=
  exists s0 t, initial_state p s0 /\ Star (semantics2 p) s0 t s.

(** In a program that never goes wrong, every state on the way can go on
    or has finished.  Excluded middle is used to turn "not stuck" into
    "finished or able to step". *)
Lemma reachable_safe p s :
  never_goes_wrong p -> reachable p s -> safe (semantics2 p) s.
Proof.
  intros N (s0 & t & I & S) s' S'.
  destruct (classic ((exists r, final_state s' r) \/
                     (exists t' s'', Step (semantics2 p) s' t' s'')))
    as [Yes | No]; [exact Yes |].
  exfalso. apply (N (Goes_wrong t)).
  eapply program_runs; [exact I |].
  eapply state_goes_wrong.
  - eapply star_trans; [exact S | exact S' | symmetry; apply E0_right].
  - intros t' s'' St. apply No. right. eauto.
  - intros r F. apply No. left. eauto.
Qed.

Lemma reachable_step p s t s' :
  reachable p s -> Star (semantics2 p) s t s' -> reachable p s'.
Proof.
  intros (s0 & t0 & I & S) S'. exists s0, (t0 ** t). split; auto.
  eapply star_trans; eauto.
Qed.
