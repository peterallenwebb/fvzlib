(** * The census for adler32.c

    The complete list, for each function of [adler32.c] in patched zlib
    1.4, of the arithmetic that VST does not check.  See
    [proofs/lib/Census.v] for what is listed and what the statuses mean.

    Each list is stated here in full and checked by computation.  If a new
    release changes what the census finds, this file stops compiling. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs.
From Stdlib Require Import List.
From fvzlib.proofs.lib Require Import Census.
From fvzlib.proofs.adler32 Require Import adler32_clight.
Import ListNotations.

(** [adler32_z]: one item, closed by its constants.

    [n = NMAX / 16] divides the signed constants 5552 and 16. *)
Example census_adler32_z :
  census f_adler32_z =
  [ mk_item SignedDivision ByConstants
      (Ebinop Odiv (Econst_int (Int.repr 5552) tint)
                   (Econst_int (Int.repr 16) tint) tint) ].
Proof. reflexivity. Qed.

(** [adler32]: nothing. *)
Example census_adler32 : census f_adler32 = [].
Proof. reflexivity. Qed.

(** The internal combine function: one item, open.

    [len2 %= BASE] takes the remainder of the signed 64-bit [len2].  In the
    1990 C standard the result is implementation-defined if [len2] is
    negative.  The statement comes after an early return for negative
    [len2], so the value is never negative there.  That has to be proven,
    and it is, in [CombineGuarded.v]. *)
Example census_combine_internal :
  census f_adler32_combine_ =
  [ mk_item SignedDivision Open
      (Ebinop Omod (Etempvar _len2 tlong)
                   (Econst_int (Int.repr 65521) tuint) tlong) ].
Proof. reflexivity. Qed.

(** [adler32_combine] and [adler32_combine64]: nothing. *)
Example census_adler32_combine : census f_adler32_combine = [].
Proof. reflexivity. Qed.

Example census_adler32_combine64 : census f_adler32_combine64 = [].
Proof. reflexivity. Qed.
