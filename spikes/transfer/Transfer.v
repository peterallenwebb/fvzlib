(** * Spike: what can be carried back to the original function

    This file checks by machine where a goto goes in CompCert's semantics.
    The conclusions of the spike are in README.md in this directory.

    The other fact the spike rests on is a lemma that VST itself proves, in
    [floyd/SeparationLogicAsLogic.v] of VST 2.17:

<<
    Lemma semax_Sgoto_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R l,
      @semax CS Espec Delta P (Sgoto l) R ->
      local (tc_environ Delta) && (allp_fun_id Delta && P)
        |-- |={Ensembles.Full_set}=> FF.
>>

    Whatever derivation proves a triple for [goto l], its precondition
    entails falsehood.  So a function with a reachable goto has no VST
    contract.  The lemma sits inside a module that VST does not export
    under a usable name, so it is quoted here and not checked by this
    file. *)

Require Import VST.floyd.proofauto.
Require Import toy GotoElim toy_nogoto.

(** ** In CompCert's semantics, the goto runs the cleanup code

    In the original toy function, [goto leave] continues with the labeled
    statement, followed by the statements after it, under the continuation
    of the enclosing call.  The loop the jump came from is discarded.  This
    is exactly the code that the transformation copies to the jump site. *)
Lemma toy_goto_target (k : cont) :
  find_label _leave (fn_body f_count_down) (call_cont k)
  = Some (Sassign (Ederef (Etempvar _out (tptr tuint)) tuint)
                  (Etempvar _steps tuint),
          Kseq (Sreturn (Some (Etempvar _n tuint))) (call_cont k)).
Proof. reflexivity. Qed.

(** The cleanup code that the transformation found is those same two
    statements in sequence. *)
Lemma toy_tail :
  find_tail _leave (fn_body f_count_down)
  = Some (Ssequence
            (Sassign (Ederef (Etempvar _out (tptr tuint)) tuint)
                     (Etempvar _steps tuint))
            (Sreturn (Some (Etempvar _n tuint)))).
Proof. reflexivity. Qed.

Print Assumptions toy_goto_target.
