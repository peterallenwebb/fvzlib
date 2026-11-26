(** * Adler-32: the functions with ticks added

    The five functions of [adler32.c], each with a tick on entry and at
    the start of every loop iteration.  They are computed from the output
    of clightgen by [instrument_function], not written by hand.

    Erasing the ticks gives back each original body exactly.  The examples
    at the end check that by computation.

    The cost contracts are proven about these functions.  Nothing here is
    compiled or shipped: the counter exists only so that a proof can count. *)

From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs.
From fvzlib.proofs.lib Require Import Ticks.
From fvzlib.proofs.adler32 Require Import adler32_clight.

(** The names listed are left folded, so the result stays readable.  They
    are the identifiers of this source file.  CompCert's built-in functions
    are not listed.  Which of them exist depends on the target, and no
    function of [adler32.c] mentions one. *)
Ltac instrument f :=
  let r := eval cbv -[_adler _adler1 _adler2 _adler32 _adler32_combine _adler32_combine64 _adler32_combine_ _adler32_z _buf _len _len2 _main _n _rem _sum1 _sum2 _t'1 _t'10 _t'11 _t'12 _t'13 _t'14 _t'15 _t'16 _t'17 _t'18 _t'19 _t'2 _t'20 _t'21 _t'22 _t'23 _t'24 _t'25 _t'26 _t'27 _t'28 _t'29 _t'3 _t'30 _t'31 _t'32 _t'33 _t'34 _t'35 _t'36 _t'37 _t'38 _t'39 _t'4 _t'40 _t'5 _t'6 _t'7 _t'8 _t'9
                      _fvz_ticks _fvz_t _fvz_exhausted
                      tuchar tuint tint tulong tlong tptr tvoid
                      Int.repr Int64.repr cc_default]
           in (instrument_function f) in
  exact r.

Definition f_adler32_z_ticked : function := ltac:(instrument f_adler32_z).
Definition f_adler32_ticked : function := ltac:(instrument f_adler32).
Definition f_adler32_combine__ticked : function :=
  ltac:(instrument f_adler32_combine_).
Definition f_adler32_combine_ticked : function :=
  ltac:(instrument f_adler32_combine).
Definition f_adler32_combine64_ticked : function :=
  ltac:(instrument f_adler32_combine64).

(** Each is what [instrument_function] gives. *)
Example ticked_adler32_z :
  f_adler32_z_ticked = instrument_function f_adler32_z.
Proof. reflexivity. Qed.
Example ticked_adler32 :
  f_adler32_ticked = instrument_function f_adler32.
Proof. reflexivity. Qed.
Example ticked_combine_ :
  f_adler32_combine__ticked = instrument_function f_adler32_combine_.
Proof. reflexivity. Qed.
Example ticked_combine :
  f_adler32_combine_ticked = instrument_function f_adler32_combine.
Proof. reflexivity. Qed.
Example ticked_combine64 :
  f_adler32_combine64_ticked = instrument_function f_adler32_combine64.
Proof. reflexivity. Qed.

(** Erasing the ticks gives back the original bodies. *)
Example erase_adler32_z :
  erase_ticks (fn_body f_adler32_z_ticked) = fn_body f_adler32_z.
Proof. reflexivity. Qed.
Example erase_adler32 :
  erase_ticks (fn_body f_adler32_ticked) = fn_body f_adler32.
Proof. reflexivity. Qed.
Example erase_combine_ :
  erase_ticks (fn_body f_adler32_combine__ticked) = fn_body f_adler32_combine_.
Proof. reflexivity. Qed.
Example erase_combine :
  erase_ticks (fn_body f_adler32_combine_ticked) = fn_body f_adler32_combine.
Proof. reflexivity. Qed.
Example erase_combine64 :
  erase_ticks (fn_body f_adler32_combine64_ticked)
  = fn_body f_adler32_combine64.
Proof. reflexivity. Qed.
