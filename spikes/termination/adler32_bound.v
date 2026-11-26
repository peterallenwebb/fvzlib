(** * The step bound applies to the instrumented Adler-32 functions

    [bounded_ticks_bound_steps], proven in [../transfer/TickBound.v], is
    about programs whose functions all have the instrumented form.  This
    file checks that the five instrumented functions of [adler32.c] have
    that form, computes their sizes, and states the bound for a program
    made of them. *)

From compcert Require Import Coqlib AST Ctypes Globalenvs Clight.
From Stdlib Require Import List Lia.
From fvzlib.proofs.lib Require Import Ticks.
Require Import adler32 adler32_ticked TickStatements TickBound.
Import ListNotations.
Local Open Scope nat_scope.

Definition ticked_functions : list function :=
  [f_adler32_z_ticked; f_adler32_ticked; f_adler32_combine__ticked;
   f_adler32_combine_ticked; f_adler32_combine64_ticked].

(** None of the five original bodies has a jump or a label, so each
    instrumented function has the form the theorem asks for. *)
Lemma all_instrumented f : In f ticked_functions -> instrumented f.
Proof.
  simpl. intros [<- | [<- | [<- | [<- | [<- | []]]]]].
  - exact (instrument_function_instrumented f_adler32_z eq_refl).
  - exact (instrument_function_instrumented f_adler32 eq_refl).
  - exact (instrument_function_instrumented f_adler32_combine_ eq_refl).
  - exact (instrument_function_instrumented f_adler32_combine eq_refl).
  - exact (instrument_function_instrumented f_adler32_combine64 eq_refl).
Qed.

(** Their sizes, in the order of the list.  The largest is [adler32_z],
    with its two loops that are unrolled sixteen times. *)
Example sizes :
  map (fun f => size (fn_body f)) ticked_functions = [689; 24; 74; 24; 24].
Proof. reflexivity. Qed.

Lemma all_small f : In f ticked_functions -> size (fn_body f) <= 689.
Proof.
  intros H.
  pose proof (in_map (fun f => size (fn_body f)) _ _ H) as Hin.
  rewrite sizes in *. simpl in *. lia.
Qed.

(** Take any program whose functions are among these five.  Start one of
    them.  An execution that has spent [c] ticks has taken at most
    [689 * (c + 1) + 2] steps.

    The cost contracts proven in this directory bound the ticks a call
    spends: at most [len / 5552 + len / 16 + 19] for [adler32_z].  Putting
    the two together would bound the steps of a call by a linear function
    of [len].  That last link is not made here.  The cost contracts are
    statements in VST's logic about the value of the counter, and this
    theorem counts steps of CompCert's semantics.  Joining them needs
    VST's soundness theorem, and the second theorem of
    [TickStatements.v] to reach the code without ticks. *)
Theorem adler32_steps_bounded (ge : genv) entry :
  (forall b f, Genv.find_funct_ptr ge b = Some (Internal f) ->
               In f ticked_functions) ->
  forall b fd args m s n c,
    Genv.find_funct_ptr ge b = Some fd ->
    run ge entry (Callstate fd args Kstop m) n c s ->
    n <= 689 * (c + 1) + 2.
Proof.
  intros Hin.
  apply (bounded_ticks_bound_steps_holds ge entry 689).
  intros b f Hf. split; [apply all_instrumented | apply all_small]; eauto.
Qed.
