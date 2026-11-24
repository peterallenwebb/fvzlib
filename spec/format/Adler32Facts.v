(** * Adler-32: facts about the format specification (Layer 1)

    Nothing in this file needs to be read to understand what is claimed.  It
    is evidence that the definitions in [Adler32.v] say what RFC 1950 says.

    Main results:

    - [update_1]: the sample-code reading and the prose reading agree.
    - [s2_unreduced]: an ambiguity in the prose is harmless.
    - [second_sum_abc]: the worked example in section 8.2 of the RFC holds.
    - [update_adler32], [update_app]: a checksum can be computed in pieces.
    - [adler32_range]: every checksum fits in 32 bits.
    - [s1_app], [s2_app]: the checksum of a concatenation, in closed form.

    This file may depend on the Rocq standard library and Layer 1 only. *)

From Stdlib Require Import ZArith List Lia.
From fvzlib.format Require Import Adler32.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Arithmetic modulo [base] *)

Lemma base_nonzero : base <> 0.
Proof. discriminate. Qed.

Lemma base_pos : 0 < base.
Proof. reflexivity. Qed.

Lemma mod_eq_intro x y k : x = y + k * base -> x mod base = y mod base.
Proof. intros ->. apply Z_mod_plus_full. Qed.

Lemma mod_decomp t : exists q, t mod base = t - q * base.
Proof.
  exists (t / base). pose proof (Z_div_mod_eq_full t base). lia.
Qed.

(** ** Sums and prefixes *)

Lemma sum_cons x l : sum (x :: l) = x + sum l.
Proof. reflexivity. Qed.

Lemma sum_app l1 l2 : sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  induction l1 as [|x l1 IH]; [reflexivity|].
  cbn [app]. rewrite !sum_cons, IH. ring.
Qed.

Lemma sum_map_mod {A} (f : A -> Z) (L : list A) :
  sum (map (fun p => f p mod base) L) mod base = sum (map f L) mod base.
Proof.
  induction L as [|p L IH]; [reflexivity|].
  cbn [map]. rewrite !sum_cons.
  rewrite Z.add_mod_idemp_l by apply base_nonzero.
  rewrite <- Z.add_mod_idemp_r by apply base_nonzero.
  rewrite IH.
  rewrite Z.add_mod_idemp_r by apply base_nonzero.
  reflexivity.
Qed.

Lemma sum_map_add {A} (f : A -> Z) (c : Z) (L : list A) :
  sum (map (fun p => f p + c) L) = sum (map f L) + Z.of_nat (length L) * c.
Proof.
  induction L as [|p L IH]; [reflexivity|].
  cbn [map length]. rewrite !sum_cons, IH. lia.
Qed.

Lemma prefixes_length l : length (prefixes l) = length l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [prefixes length]. rewrite length_map, IH. reflexivity.
Qed.

(** [prefixes] really is the list of non-empty prefixes, shortest first. *)
Theorem prefixes_firstn l :
  prefixes l = map (fun k => firstn k l) (seq 1 (length l)).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [prefixes length seq map firstn]. f_equal.
  rewrite IH, map_map, <- (seq_shift (length l) 1), map_map. reflexivity.
Qed.

Lemma prefixes_app a b :
  prefixes (a ++ b) = prefixes a ++ map (app a) (prefixes b).
Proof.
  induction a as [|x a IH].
  - exact (eq_sym (map_id (prefixes b))).
  - cbn [app prefixes]. rewrite IH, map_app, map_map. reflexivity.
Qed.

(** ** The loop of the sample code, in closed form *)

(** The loop body without the reductions modulo [base]. *)
Definition raw_step (state : Z * Z) (byte : Z) : Z * Z :=
  (fst state + byte, snd state + (fst state + byte)).

Lemma step_mod a b x :
  step (a mod base, b mod base) x = ((a + x) mod base, (b + (a + x)) mod base).
Proof.
  unfold step. cbn [fst snd]. cbv zeta.
  rewrite Z.add_mod_idemp_l by apply base_nonzero.
  f_equal.
  rewrite Z.add_mod_idemp_l by apply base_nonzero.
  rewrite Z.add_mod_idemp_r by apply base_nonzero.
  reflexivity.
Qed.

Lemma fold_step_mod l : forall a b,
  fold_left step l (a mod base, b mod base) =
  (fst (fold_left raw_step l (a, b)) mod base,
   snd (fold_left raw_step l (a, b)) mod base).
Proof.
  induction l as [|x l IH]; intros a b; cbn [fold_left]; [reflexivity|].
  rewrite step_mod, IH. reflexivity.
Qed.

Lemma fold_raw l : forall a b,
  fold_left raw_step l (a, b) =
  (a + sum l, b + sum (map (fun p => a + sum p) (prefixes l))).
Proof.
  induction l as [|x l IH]; intros a b.
  - cbn. f_equal; lia.
  - cbn [fold_left].
    change (raw_step (a, b) x) with (a + x, b + (a + x)).
    rewrite IH. cbn [prefixes map]. rewrite map_map, !sum_cons.
    rewrite (map_ext (fun p => a + sum (x :: p)) (fun p => a + x + sum p))
      by (intros; rewrite sum_cons; lia).
    change (sum []) with 0.
    f_equal; lia.
Qed.

Lemma fold_step_closed l a b :
  fold_left step l (a mod base, b mod base) =
  ((a + sum l) mod base,
   (b + sum (map (fun p => a + sum p) (prefixes l))) mod base).
Proof. rewrite fold_step_mod, fold_raw. reflexivity. Qed.

(** ** An ambiguity in the prose is harmless

    "s2 is the sum of all s1 values. Both sums are done modulo 65521."  This
    does not say whether the s1 values are reduced before they are added.
    [s2] adds the reduced values.  Adding the unreduced values gives the same
    result. *)
Theorem s2_unreduced bytes :
  s2 bytes = sum (map (fun p => 1 + sum p) (prefixes bytes)) mod base.
Proof.
  unfold s2. rewrite Z.add_0_l.
  apply (sum_map_mod (fun p => 1 + sum p)).
Qed.

(** RFC 1950, section 8.2: "If the bytes are a, b, c, the second sum is
    3a + 2b + c + 3, and so is position and order sensitive". *)
Theorem second_sum_abc a b c : s2 [a; b; c] = (3 * a + 2 * b + c + 3) mod base.
Proof.
  rewrite s2_unreduced. cbn [prefixes map]. rewrite !sum_cons.
  change (sum []) with 0. f_equal. ring.
Qed.

(** ** The two readings of the RFC agree *)

Theorem fold_step_init bytes :
  fold_left step bytes (1, 0) = (s1 bytes, s2 bytes).
Proof.
  change (1, 0) with (1 mod base, 0 mod base).
  rewrite fold_step_closed, s2_unreduced. reflexivity.
Qed.

(** RFC 1950, section 9: "Return the adler32 of the bytes buf[0..len-1]:
    return update_adler32(1L, buf, len);" *)
Theorem update_1 bytes : update 1 bytes = adler32 bytes.
Proof.
  unfold update. change (low16 1, high16 1) with (1, 0).
  rewrite fold_step_init. reflexivity.
Qed.

(** ** Ranges *)

Lemma s1_range bytes : 0 <= s1 bytes < base.
Proof. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma s2_range bytes : 0 <= s2 bytes < base.
Proof. apply Z.mod_pos_bound. reflexivity. Qed.

(** Every Adler-32 checksum fits in an unsigned 32-bit integer. *)
Theorem adler32_range bytes : 0 <= adler32 bytes < 4294967296.
Proof.
  unfold adler32. pose proof (s1_range bytes). pose proof (s2_range bytes).
  unfold base in *. lia.
Qed.

Lemma low16_pack a b : 0 <= a < 65536 -> low16 (b * 65536 + a) = a.
Proof.
  intros. unfold low16. rewrite Z.add_comm, Z_mod_plus_full.
  apply Z.mod_small. assumption.
Qed.

Lemma high16_pack a b :
  0 <= a < 65536 -> 0 <= b < 65536 -> high16 (b * 65536 + a) = b.
Proof.
  intros. unfold high16.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small a) by lia.
  rewrite Z.add_0_r. apply Z.mod_small. assumption.
Qed.

Lemma low16_adler32 bytes : low16 (adler32 bytes) = s1 bytes.
Proof.
  pose proof (s1_range bytes). unfold base in *.
  apply low16_pack. lia.
Qed.

Lemma high16_adler32 bytes : high16 (adler32 bytes) = s2 bytes.
Proof.
  pose proof (s1_range bytes). pose proof (s2_range bytes). unfold base in *.
  apply high16_pack; lia.
Qed.

Lemma low16_range adler : 0 <= low16 adler < 65536.
Proof. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma high16_range adler : 0 <= high16 adler < 65536.
Proof. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma fold_step_range l : forall state,
  0 <= fst state < 65536 -> 0 <= snd state < 65536 ->
  0 <= fst (fold_left step l state) < 65536 /\
  0 <= snd (fold_left step l state) < 65536.
Proof.
  induction l as [|x l IH]; intros state H1 H2; cbn [fold_left]; [tauto|].
  apply IH; unfold step; cbn [fst snd]; cbv zeta.
  - pose proof (Z.mod_pos_bound (fst state + x) base base_pos).
    unfold base in *. lia.
  - pose proof (Z.mod_pos_bound
                  (snd state + (fst state + x) mod base) base base_pos).
    unfold base in *. lia.
Qed.

(** [update] returns a 32-bit value whatever it is given. *)
Theorem update_range adler bytes : 0 <= update adler bytes < 4294967296.
Proof.
  unfold update.
  destruct (fold_step_range bytes (low16 adler, high16 adler)
              (low16_range adler) (high16_range adler)).
  lia.
Qed.

(** ** Computing a checksum in pieces *)

Theorem update_app adler a b :
  update (update adler a) b = update adler (a ++ b).
Proof.
  unfold update. rewrite fold_left_app.
  destruct (fold_step_range a (low16 adler, high16 adler)
              (low16_range adler) (high16_range adler)) as [H1 H2].
  destruct (fold_left step a (low16 adler, high16 adler)) as [x y].
  cbn [fst snd] in *.
  rewrite low16_pack, high16_pack by assumption. reflexivity.
Qed.

(** Continuing from the checksum of [a] over [b] gives the checksum of
    [a ++ b]. *)
Theorem update_adler32 a b : update (adler32 a) b = adler32 (a ++ b).
Proof. rewrite <- !update_1. apply update_app. Qed.

(** The checksum of no bytes is 1. *)
Theorem adler32_nil : adler32 [] = 1.
Proof. reflexivity. Qed.

(** Updating with no bytes changes nothing, for any 32-bit value. *)
Theorem update_nil adler : 0 <= adler < 4294967296 -> update adler [] = adler.
Proof.
  intros. unfold update, low16, high16. cbn [fold_left fst snd].
  rewrite (Z.mod_small (adler / 65536)).
  - pose proof (Z_div_mod_eq_full adler 65536). lia.
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(** ** The checksum of a concatenation, in closed form *)

Theorem s1_app a b : s1 (a ++ b) = (s1 a + s1 b - 1) mod base.
Proof.
  unfold s1. rewrite sum_app.
  destruct (mod_decomp (1 + sum a)) as [q1 ->].
  destruct (mod_decomp (1 + sum b)) as [q2 ->].
  apply mod_eq_intro with (k := q1 + q2). ring.
Qed.

Theorem s2_app a b :
  s2 (a ++ b) = (s2 a + s2 b + Z.of_nat (length b) * (s1 a - 1)) mod base.
Proof.
  rewrite !s2_unreduced. unfold s1.
  rewrite prefixes_app, map_app, sum_app, map_map.
  rewrite (map_ext (fun p => 1 + sum (a ++ p)) (fun p => (1 + sum p) + sum a))
    by (intros; rewrite sum_app; ring).
  rewrite (sum_map_add (fun p => 1 + sum p)), prefixes_length.
  destruct (mod_decomp (sum (map (fun p => 1 + sum p) (prefixes a))))
    as [q1 ->].
  destruct (mod_decomp (sum (map (fun p => 1 + sum p) (prefixes b))))
    as [q2 ->].
  destruct (mod_decomp (1 + sum a)) as [q3 ->].
  apply mod_eq_intro with (k := q1 + q2 + Z.of_nat (length b) * q3). ring.
Qed.
