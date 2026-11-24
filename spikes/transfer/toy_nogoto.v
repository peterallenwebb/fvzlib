(** The toy function with its goto removed.  Computed, not written by hand. *)
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs.
Require Import toy GotoElim.

(* The names listed are kept folded so that the result stays readable.
   Everything else, including the label comparison, is computed. *)
Definition f_count_down_nogoto : function :=
  ltac:(let r := eval cbv -[_n _stop _out _steps tuint tint tptr Int.repr
                             cc_default]
                 in (transform_function _leave f_count_down) in
        match r with Some ?f => exact f end).

(** The original has a goto.  The transformed function has none. *)
Example original_has_goto : goto_free (fn_body f_count_down) = false.
Proof. reflexivity. Qed.

Example transformed_is_goto_free : goto_free (fn_body f_count_down_nogoto) = true.
Proof. reflexivity. Qed.

(** Applying the transformation again finds nothing to do. *)
Example no_label_left : find_tail _leave (fn_body f_count_down_nogoto) = None.
Proof. reflexivity. Qed.
