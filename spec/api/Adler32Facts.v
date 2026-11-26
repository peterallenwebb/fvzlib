(** * Adler-32: facts about the API behavior (Layer 2)

    Nothing in this file needs to be read to understand what is claimed.  It
    is evidence that the specifications in [Adler32.v] are sound and usable.

    Main results:

    - [adler32_spec_satisfiable], [adler32_combine_spec_satisfiable]: each
      specification can be met for every input, so none is contradictory.
    - [adler32_spec_deterministic], [adler32_combine_spec_deterministic]:
      where the manual makes a promise, it fixes the result.
    - [adler32_initial_value]: the required initial value is 1.
    - [adler32_spec_range]: results are 32-bit values.
    - [checksum_form_iff]: a value is the checksum of some data exactly
      when it fits in 32 bits and both of its halves are below 65521.
    - [usage_example]: the usage example in the manual computes the checksum
      of all the data, however it is split into buffers.
    - [adler32_combine_spec_negative]: a negative length allows any result.

    This file may depend on the Rocq standard library and Layers 1 and 2
    only. *)

From Stdlib Require Import ZArith List Lia.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
Import ListNotations.
Local Open Scope Z_scope.

Lemma all_bytes_app a b : all_bytes a -> all_bytes b -> all_bytes (a ++ b).
Proof. intros. apply Forall_app. split; assumption. Qed.

Lemma all_bytes_nil : all_bytes [].
Proof. constructor. Qed.

(** ** adler32 and adler32_z *)

(** "If buf is Z_NULL, this function returns the required initial value for
    the checksum."  That value is 1. *)
Theorem adler32_initial_value adler result :
  adler32_spec adler None result <-> result = 1.
Proof.
  unfold adler32_spec, running_checksum. rewrite adler32_nil.
  split; [tauto | intros ->; split; [apply all_bytes_nil | reflexivity]].
Qed.

(** The specification can always be met.  A function that returns 1 for
    [Z_NULL], and otherwise runs the RFC sample code, meets it. *)
Definition adler32_reference (adler : Z) (buf : option (list Z)) : Z :=
  match buf with
  | None => 1
  | Some bytes => update adler bytes
  end.

Theorem adler32_reference_meets_spec adler buf :
  adler32_spec adler buf (adler32_reference adler buf).
Proof.
  destruct buf as [bytes|]; cbn.
  - intros Hbytes earlier [Hearlier ->]. split.
    + apply all_bytes_app; assumption.
    + apply update_adler32.
  - split; [apply all_bytes_nil | reflexivity].
Qed.

Theorem adler32_spec_satisfiable adler buf :
  exists result, adler32_spec adler buf result.
Proof. eexists. apply adler32_reference_meets_spec. Qed.

(** Where the manual makes a promise, the result is fixed. *)
Theorem adler32_spec_deterministic adler earlier bytes r1 r2 :
  running_checksum adler earlier ->
  all_bytes bytes ->
  adler32_spec adler (Some bytes) r1 ->
  adler32_spec adler (Some bytes) r2 ->
  r1 = r2.
Proof.
  intros Hadler Hbytes H1 H2.
  destruct (H1 Hbytes earlier Hadler) as [_ ->].
  destruct (H2 Hbytes earlier Hadler) as [_ ->].
  reflexivity.
Qed.

(** "An Adler-32 value is in the range of a 32-bit unsigned integer." *)
Theorem running_checksum_range adler data :
  running_checksum adler data -> 0 <= adler < 4294967296.
Proof. intros [_ ->]. apply adler32_range. Qed.

Theorem adler32_spec_range adler earlier bytes result :
  running_checksum adler earlier ->
  all_bytes bytes ->
  adler32_spec adler (Some bytes) result ->
  0 <= result < 4294967296.
Proof.
  intros Hadler Hbytes H.
  eapply running_checksum_range. apply (H Hbytes earlier Hadler).
Qed.

(** Updating with no bytes returns the checksum unchanged. *)
Theorem adler32_spec_no_bytes adler earlier result :
  running_checksum adler earlier ->
  adler32_spec adler (Some []) result ->
  result = adler.
Proof.
  intros Hadler H.
  destruct (H all_bytes_nil earlier Hadler) as [_ ->].
  destruct Hadler as [_ ->]. rewrite app_nil_r. reflexivity.
Qed.

(** ** Which values are checksums

    The manual's promise for a buffer holds when the checksum argument is
    the checksum of some earlier data.  A caller who has only the value can
    still tell whether that is so: the value must fit in 32 bits, and each
    of its halves must be below 65521.  Every such value is the checksum of
    some sequence of bytes. *)

Definition checksum_form (adler : Z) : Prop :=
  0 <= adler < 4294967296 /\ low16 adler < base /\ high16 adler < base.

Lemma sum_repeat x n : sum (repeat x n) = Z.of_nat n * x.
Proof. induction n; cbn [repeat]; [reflexivity | rewrite sum_cons; lia]. Qed.

Lemma all_bytes_repeat x n : is_byte x -> all_bytes (repeat x n).
Proof. intros. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst. assumption. Qed.

(** Zero bytes leave the first sum at 1 and add 1 to the second each. *)
Lemma s1_zeros n : s1 (repeat 0 n) = 1.
Proof. unfold s1. rewrite sum_repeat, Z.mul_0_r. reflexivity. Qed.

Lemma s2_zeros n : s2 (repeat 0 n) = Z.of_nat n mod base.
Proof.
  induction n as [|n IH]; [reflexivity |].
  change (repeat 0 (S n)) with ([0] ++ repeat 0 n).
  rewrite s2_app, IH, repeat_length.
  change (s1 [0]) with 1. change (s2 [0]) with 1.
  rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r, Zplus_mod_idemp_r.
  f_equal. lia.
Qed.

(** Bytes of value 1 add 1 to the first sum each. *)
Lemma s1_ones n : s1 (repeat 1 n) = (1 + Z.of_nat n) mod base.
Proof. unfold s1. rewrite sum_repeat, Z.mul_1_r. reflexivity. Qed.

(** A value with the form of a checksum is the checksum of this data:
    enough zero bytes to set the second sum, then enough bytes of value 1
    to set the first. *)
Theorem checksum_form_iff adler :
  (exists data, running_checksum adler data) <-> checksum_form adler.
Proof.
  split.
  - intros [data [_ ->]]. unfold checksum_form.
    rewrite low16_adler32, high16_adler32.
    pose proof (adler32_range data). pose proof (s1_range data).
    pose proof (s2_range data). lia.
  - intros (Hrange & Hlow & Hhigh).
    pose proof (low16_range adler) as Ha. pose proof (high16_range adler) as Hb.
    assert (E : adler = high16 adler * 65536 + low16 adler).
    { unfold high16, low16.
      rewrite (Z.mod_small (adler / 65536))
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      pose proof (Z_div_mod_eq_full adler 65536). lia. }
    set (a := low16 adler) in *. set (b := high16 adler) in *.
    set (ones := repeat 1 (Z.to_nat ((a - 1) mod base))).
    set (zeros := repeat 0 (Z.to_nat ((b - s2 ones) mod base))).
    exists (zeros ++ ones). split.
    + apply all_bytes_app; apply all_bytes_repeat; unfold is_byte; lia.
    + pose proof (Z.mod_pos_bound (a - 1) base base_pos).
      pose proof (Z.mod_pos_bound (b - s2 ones) base base_pos).
      rewrite E. unfold adler32. f_equal; [f_equal |].
      * rewrite s2_app. subst zeros. rewrite s2_zeros, s1_zeros, Z2Nat.id by lia.
        rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r, Z.mod_mod by apply base_nonzero.
        rewrite Zplus_mod_idemp_l.
        replace (b - s2 ones + s2 ones) with b by lia.
        symmetry. apply Z.mod_small. lia.
      * rewrite s1_app. subst zeros ones. rewrite s1_zeros, s1_ones, Z2Nat.id by lia.
        replace (1 + (1 + (a - 1) mod base) mod base - 1)
          with ((1 + (a - 1) mod base) mod base) by lia.
        rewrite Z.mod_mod by apply base_nonzero. rewrite Zplus_mod_idemp_r.
        replace (1 + (a - 1)) with a by lia.
        symmetry. apply Z.mod_small. lia.
Qed.

(** ** The usage example in the manual

<<
     uLong adler = adler32(0L, Z_NULL, 0);

     while (read_buffer(buffer, length) != EOF) {
       adler = adler32(adler, buffer, length);
     }
     if (adler != original_adler) error();
>>

    [fed_in_order adler buffers final] says that calling [adler32] once for
    each buffer in turn, starting from [adler], ends with [final]. *)
Fixpoint fed_in_order (adler : Z) (buffers : list (list Z)) (final : Z) : Prop :=
  match buffers with
  | [] => final = adler
  | buffer :: rest =>
      exists next,
        adler32_spec adler (Some buffer) next /\ fed_in_order next rest final
  end.

Lemma fed_in_order_running buffers : forall adler earlier final,
  Forall all_bytes buffers ->
  running_checksum adler earlier ->
  fed_in_order adler buffers final ->
  running_checksum final (earlier ++ concat buffers).
Proof.
  induction buffers as [|buffer rest IH]; intros adler earlier final Hb Hadler H.
  - cbn in *. subst final. rewrite app_nil_r. assumption.
  - cbn [fed_in_order concat] in *. destruct H as [next [Hnext Hrest]].
    inversion Hb as [|? ? Hbuffer Hrest_bytes]; subst.
    rewrite app_assoc.
    apply (IH next (earlier ++ buffer) final Hrest_bytes); [|assumption].
    apply (Hnext Hbuffer earlier Hadler).
Qed.

(** Starting from the [Z_NULL] call and feeding the buffers in order gives
    the checksum of all the data.  The result does not depend on how the
    data was split into buffers. *)
Theorem usage_example anything initial buffers final :
  Forall all_bytes buffers ->
  adler32_spec anything None initial ->
  fed_in_order initial buffers final ->
  final = adler32 (concat buffers).
Proof.
  intros Hb Hinit Hfed.
  destruct (fed_in_order_running buffers initial [] final Hb Hinit Hfed)
    as [_ ->].
  reflexivity.
Qed.

(** ** adler32_combine *)

(** The specification can always be met.  This formula meets it. *)
Definition combine_reference (adler1 adler2 len2 : Z) : Z :=
  ((high16 adler1 + high16 adler2 + len2 * (low16 adler1 - 1)) mod base) * 65536
  + (low16 adler1 + low16 adler2 - 1) mod base.

Theorem combine_reference_correct a b :
  combine_reference (adler32 a) (adler32 b) (Z.of_nat (length b))
  = adler32 (a ++ b).
Proof.
  unfold combine_reference.
  rewrite !low16_adler32, !high16_adler32.
  unfold adler32 at 1. rewrite s1_app, s2_app. reflexivity.
Qed.

Theorem combine_reference_meets_spec adler1 adler2 len2 :
  adler32_combine_spec adler1 adler2 len2 (combine_reference adler1 adler2 len2).
Proof.
  intros seq1 seq2 [H1 ->] [H2 ->] ->. split.
  - apply all_bytes_app; assumption.
  - apply combine_reference_correct.
Qed.

Theorem adler32_combine_spec_satisfiable adler1 adler2 len2 :
  exists result, adler32_combine_spec adler1 adler2 len2 result.
Proof. eexists. apply combine_reference_meets_spec. Qed.

(** Where the manual makes a promise, the result is fixed. *)
Theorem adler32_combine_spec_deterministic adler1 adler2 seq1 seq2 r1 r2 :
  running_checksum adler1 seq1 ->
  running_checksum adler2 seq2 ->
  adler32_combine_spec adler1 adler2 (Z.of_nat (length seq2)) r1 ->
  adler32_combine_spec adler1 adler2 (Z.of_nat (length seq2)) r2 ->
  r1 = r2.
Proof.
  intros Ha Hb H1 H2.
  destruct (H1 seq1 seq2 Ha Hb eq_refl) as [_ ->].
  destruct (H2 seq1 seq2 Ha Hb eq_refl) as [_ ->].
  reflexivity.
Qed.

(** "If len2 is negative, the result has no meaning or utility." *)
Theorem adler32_combine_spec_negative adler1 adler2 len2 result :
  len2 < 0 -> adler32_combine_spec adler1 adler2 len2 result.
Proof. intros Hneg seq1 seq2 _ _ Hlen. lia. Qed.
