(** The goto-free toy function with ticks added.  Computed, not written by
    hand. *)
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs.
From fvzlib.proofs.lib Require Import Ticks.
Require Import toy toy_nogoto.

Definition f_count_down_ticked : function :=
  ltac:(let r := eval cbv -[_n _stop _out _steps _fvz_ticks _fvz_t
                             _fvz_exhausted tuint tint tulong tptr
                             Int.repr Int64.repr cc_default]
                 in (instrument_function f_count_down_nogoto) in
        exact r).

(** Erasing the ticks gives back exactly the function that was instrumented. *)
Example erase_round_trip :
  erase_ticks (fn_body f_count_down_ticked) = fn_body f_count_down_nogoto.
Proof. reflexivity. Qed.
