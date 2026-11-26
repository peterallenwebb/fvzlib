(** * Adler-32: the reference model against zlib, case by case

    This file is test code.  It is not part of any layer and nothing is
    proven from it.

    [tools/check_differential.py] runs the real zlib on several thousand
    inputs and writes what zlib returned to a generated file,
    [Adler32Cases.v], as a list of [case]s.  That file ends with

      Example all_agree : failures cases = [].
      Proof. vm_cast_no_check (eq_refl (@nil Z)). Qed.

    So Rocq itself evaluates the model on each input and compares the
    result with zlib's.  The model is not extracted or translated.  The
    evaluation is done by Rocq's virtual machine when the kernel checks
    the proof at [Qed].

    The inputs are held in primitive strings, which Rocq reads quickly.
    That makes this file depend on Rocq's primitive integers and strings.
    The specifications do not.

    What is compared with zlib:

    - [adler32], the prose definition of RFC 1950 (Layer 1);
    - [update], the sample code of RFC 1950 (Layer 1), through
      [adler32_reference] (Layer 2);
    - [combine_reference], the formula for a concatenation (Layer 2). *)

From Stdlib Require Import ZArith List Uint63 PrimString.
From fvzlib.format Require Import Adler32.
From fvzlib.api Require Import Adler32Facts.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Inputs *)

(** The value of a hexadecimal digit, [0-9a-f]. *)
Definition hex_digit (c : char63) : Z :=
  let n := Uint63.to_Z c in
  if n <? 58 then n - 48 else n - 87.

(** The [count] bytes written by the hexadecimal digits of [s] that end
    just before position [i], put in front of [acc]. *)
Fixpoint bytes_before (s : string) (count : nat) (i : int) (acc : list Z)
    : list Z :=
  match count with
  | O => acc
  | S n =>
      let j := (i - 2)%uint63 in
      bytes_before s n j
        ((hex_digit (get s j) * 16 + hex_digit (get s (j + 1)%uint63)) :: acc)
  end.

(** The bytes that a string of hexadecimal digits writes out, two digits
    to a byte. *)
Definition bytes_of_hex (s : string) : list Z :=
  let digits := PrimString.length s in
  bytes_before s (Z.to_nat (Uint63.to_Z digits / 2)) digits [].

Example bytes_of_hex_example :
  bytes_of_hex "00ff1a7e"%pstring = [0; 255; 26; 126].
Proof. vm_compute. reflexivity. Qed.

(** [count] bytes: [first], [first + step], [first + 2 * step], and so on,
    each reduced to a byte. *)
Fixpoint run (count : nat) (first step : Z) : list Z :=
  match count with
  | O => []
  | S n => (first mod 256) :: run n (first + step) step
  end.

(** An input to zlib.  Short inputs are written out.  Long regular ones
    are described, to keep the generated file small. *)
Inductive data :=
| Hex (digits : string)
| Run (count first step : Z).

Definition bytes (d : data) : list Z :=
  match d with
  | Hex digits => bytes_of_hex digits
  | Run count first step => run (Z.to_nat count) first step
  end.

(** ** Cases

    Each case records calls that were made to zlib and what it returned. *)
Inductive case :=
(** [adler32(x, Z_NULL, n)] returned [result]. *)
| Initial (result : Z)
(** One call on [d], starting from the initial value, returned [result]. *)
| Whole (d : data) (result : Z)
(** The same, for an input short enough for the prose definition. *)
| Prose (d : data) (result : Z)
(** The inputs [ds] were fed in order, one call each, each call given the
    result of the one before.  The last call returned [result]. *)
| Pieces (ds : list data) (result : Z)
(** [adler32_combine(adler1, adler2, len2)] returned [result]. *)
| Combine (adler1 adler2 len2 : Z) (result : Z)
(** [d1] and [d2] were checksummed separately, giving [adler1] and
    [adler2], and combining those returned [result]. *)
| Joined (d1 d2 : data) (adler1 adler2 : Z) (result : Z).

Definition whole (d : data) : Z := adler32_reference 1 (Some (bytes d)).

Definition agrees (c : case) : bool :=
  match c with
  | Initial result => adler32_reference 0 None =? result
  | Whole d result => whole d =? result
  | Prose d result => (adler32 (bytes d) =? result) && (whole d =? result)
  | Pieces ds result =>
      fold_left (fun adler d => adler32_reference adler (Some (bytes d))) ds 1
      =? result
  | Combine adler1 adler2 len2 result =>
      combine_reference adler1 adler2 len2 =? result
  | Joined d1 d2 adler1 adler2 result =>
      (whole d1 =? adler1) && (whole d2 =? adler2)
      && (combine_reference adler1 adler2 (Z.of_nat (List.length (bytes d2)))
          =? result)
      && (adler32_reference 1 (Some (bytes d1 ++ bytes d2)) =? result)
  end.

(** The positions, from 0, of the cases where the model and zlib differ. *)
Fixpoint failures_from (n : Z) (cases : list case) : list Z :=
  match cases with
  | [] => []
  | c :: rest =>
      if agrees c then failures_from (n + 1) rest
      else n :: failures_from (n + 1) rest
  end.

Definition failures (cases : list case) : list Z := failures_from 0 cases.
