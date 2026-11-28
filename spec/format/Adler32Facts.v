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
    - [adler32_one_byte_changed]: changing one byte changes the checksum.

    This file may depend on the Rocq standard library and Layer 1 only. *)

From Stdlib Require Import ZArith List Lia.
From fvzlib.format Require Import Bytes Adler32.
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

(** ** How long the reduction can be put off

    RFC 1950, section 8.2, says the reduction modulo [base] "can be delayed
    for 5552 bytes" on accumulators that have at least 32 bits.  These
    three results make that exact.

    - [raw_fold_bounds]: how large the two sums can get with no reduction.
    - [delay_5552]: start from reduced sums and add up to 5552 bytes with
      no reduction.  Both sums stay below 2^32, and reducing them then
      gives the pair that reducing at every step gives.
    - [delay_5553_does_not_fit]: 5552 is the most.  With 5553 bytes the
      second sum can reach 2^32. *)

Lemma raw_fold_bounds l : forall a b,
  all_bytes l -> 0 <= a -> 0 <= b ->
  let n := Z.of_nat (length l) in
  let st := fold_left raw_step l (a, b) in
  0 <= fst st <= a + 255 * n /\
  0 <= 2 * snd st <= 2 * b + 2 * n * a + 255 * n * (n + 1).
Proof.
  induction l as [|x l IH]; intros a b Hbytes Ha Hb.
  - cbv zeta. cbn [fold_left length fst snd]. change (Z.of_nat 0) with 0. lia.
  - inversion Hbytes as [|? ? Hx Hl]; subst. unfold is_byte in Hx.
    cbn [fold_left]. change (raw_step (a, b) x) with (a + x, b + (a + x)).
    specialize (IH (a + x) (b + (a + x)) Hl ltac:(lia) ltac:(lia)).
    cbv zeta in *. rewrite length_cons, Nat2Z.inj_succ.
    set (n := Z.of_nat (length l)) in *.
    assert (0 <= n) by (subst n; lia).
    destruct IH as [[IH1 IH2] [IH3 IH4]].
    repeat split; try lia; nia.
Qed.

Theorem delay_5552 l a b :
  all_bytes l -> Z.of_nat (length l) <= 5552 ->
  0 <= a < base -> 0 <= b < base ->
  let st := fold_left raw_step l (a, b) in
  0 <= fst st < 4294967296 /\ 0 <= snd st < 4294967296 /\
  (fst st mod base, snd st mod base) = fold_left step l (a, b).
Proof.
  intros Hbytes Hlen Ha Hb st.
  pose proof (raw_fold_bounds l a b Hbytes ltac:(lia) ltac:(lia)) as B.
  cbv zeta in B. fold st in B.
  set (n := Z.of_nat (length l)) in *.
  assert (0 <= n) by (subst n; lia).
  unfold base in *.
  destruct B as [[B1 B2] [B3 B4]].
  assert (n * (n + 1) <= 5552 * 5553) by nia.
  assert (n * a <= 5552 * 65520) by nia.
  repeat split; try lia.
  unfold st. rewrite <- fold_step_mod.
  unfold base. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Example delay_5553_does_not_fit :
  all_bytes (repeat 255 (Z.to_nat 5553)) /\
  4294967296 <= snd (fold_left raw_step (repeat 255 (Z.to_nat 5553)) (65520, 65520)).
Proof.
  split.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst.
    unfold is_byte. lia.
  - vm_compute. discriminate.
Qed.

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

(** ** Every byte counts

    Two sequences that differ in exactly one byte have different
    checksums.  So the checksum of a sequence cannot be found without
    looking at every byte of it.  A contract for a function that returns
    the checksum must therefore let the function read every byte. *)

Theorem adler32_one_byte_changed before a b after :
  is_byte a -> is_byte b -> a <> b ->
  adler32 (before ++ a :: after) <> adler32 (before ++ b :: after).
Proof.
  unfold is_byte. intros Ha Hb Hab E.
  apply (f_equal low16) in E. rewrite !low16_adler32 in E.
  unfold s1 in E. rewrite !sum_app, !sum_cons in E.
  destruct (mod_decomp (1 + (sum before + (a + sum after)))) as [q1 E1].
  destruct (mod_decomp (1 + (sum before + (b + sum after)))) as [q2 E2].
  rewrite E1, E2 in E. unfold base in E. lia.
Qed.
