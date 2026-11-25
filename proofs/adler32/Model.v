(** * Adler-32: how the C code's arithmetic relates to the specification

    The C code does not reduce modulo 65521 after every byte.  It adds bytes
    into two unsigned accumulators and reduces only now and then.  This file
    is the mathematics that connects that to the Layer 1 definition, which
    reduces at every step.  There is no C and no separation logic here.

    - [acc] is the pair of accumulators after some bytes, with no reduction.
    - [reduced_at] is the pair the specification would have at that point.
    - [modpair_acc] says reducing [acc] gives what the specification gives.
    - [update_from_reduced] says the final pair, packed, is [update]. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.

Local Open Scope Z_scope.

(** The accumulators after the bytes at positions [lo] up to [k], starting
    from [st], with no reduction. *)
Definition acc (zs : list Z) (st : Z * Z) (lo k : Z) : Z * Z :=
  fold_left raw_step (sublist lo k zs) st.

(** Reduce both accumulators. *)
Definition modpair (st : Z * Z) : Z * Z := (fst st mod base, snd st mod base).

(** The pair the specification has after the first [k] bytes, starting from
    the two halves [a0] and [s0] of the incoming checksum. *)
Definition reduced_at (zs : list Z) (a0 s0 k : Z) : Z * Z :=
  fold_left step (sublist 0 k zs) (a0 mod base, s0 mod base).

Lemma acc_start zs st lo : acc zs st lo lo = st.
Proof. unfold acc. rewrite sublist_nil. reflexivity. Qed.

Lemma acc_step zs st lo k :
  0 <= lo <= k -> k < Zlength zs ->
  acc zs st lo (k + 1) = raw_step (acc zs st lo k) (Znth k zs).
Proof.
  intros. unfold acc.
  rewrite (sublist_split lo k (k + 1)) by lia.
  rewrite fold_left_app, sublist_len_1 by lia. reflexivity.
Qed.

Lemma acc_split zs st lo mid k :
  0 <= lo <= mid -> mid <= k <= Zlength zs ->
  acc zs st lo k = acc zs (acc zs st lo mid) mid k.
Proof.
  intros. unfold acc.
  rewrite (sublist_split lo mid k) by lia. apply fold_left_app.
Qed.

(** ** Bounds: the accumulators cannot overflow 64 bits *)

Lemma raw_fold_bounds l : forall st,
  all_bytes l -> 0 <= fst st -> 0 <= snd st ->
  fst st <= fst (fold_left raw_step l st) <= fst st + 255 * Zlength l /\
  snd st <= snd (fold_left raw_step l st)
         <= snd st + Zlength l * (fst st + 255 * Zlength l).
Proof.
  induction l as [|x l IH]; intros [a b] Hbytes Ha Hb; cbn [fst snd] in *.
  - cbn [fold_left fst snd]. rewrite Zlength_nil. lia.
  - inversion Hbytes as [|? ? Hx Hl]; subst. unfold is_byte in Hx.
    cbn [fold_left]. change (raw_step (a, b) x) with (a + x, b + (a + x)).
    specialize (IH (a + x, b + (a + x)) Hl ltac:(cbn; lia) ltac:(cbn; lia)).
    cbn [fst snd] in IH. rewrite Zlength_cons.
    pose proof (Zlength_nonneg l).
    destruct IH as [[IH1 IH2] [IH3 IH4]].
    assert (Zlength l * x <= Zlength l * 255)
      by (apply Z.mul_le_mono_nonneg_l; lia).
    repeat split; try lia; nia.
Qed.

Lemma all_bytes_sublist zs lo k : all_bytes zs -> all_bytes (sublist lo k zs).
Proof. unfold all_bytes. intros. apply Forall_sublist. assumption. Qed.

(** After at most 5552 bytes from a pair of 16-bit values, both accumulators
    are far below 2^64. *)
Lemma acc_bounds zs st lo k :
  all_bytes zs -> 0 <= lo <= k -> k <= Zlength zs -> k - lo <= 5552 ->
  0 <= fst st <= 65535 -> 0 <= snd st <= 65535 ->
  0 <= fst (acc zs st lo k) <= 1481295 /\
  0 <= snd (acc zs st lo k) <= 8224266655.
Proof.
  intros Hb Hlo Hk Hlen Ha Hs. unfold acc.
  pose proof (raw_fold_bounds (sublist lo k zs) st
                (all_bytes_sublist zs lo k Hb) ltac:(lia) ltac:(lia)) as H.
  rewrite Zlength_sublist in H by lia.
  destruct H as [[H1 H2] [H3 H4]].
  repeat split; try lia; nia.
Qed.

(** ** Reducing the accumulators gives what the specification gives *)

Lemma modpair_acc zs st lo k :
  modpair (acc zs st lo k) = fold_left step (sublist lo k zs) (modpair st).
Proof.
  unfold modpair, acc. destruct st as [a b]. cbn [fst snd].
  symmetry. apply fold_step_mod.
Qed.

Lemma fold_step_reduced l : forall st,
  0 <= fst st < base -> 0 <= snd st < base ->
  0 <= fst (fold_left step l st) < base /\ 0 <= snd (fold_left step l st) < base.
Proof.
  induction l as [|x l IH]; intros st H1 H2; cbn [fold_left]; [tauto|].
  apply IH; unfold step; cbn [fst snd]; cbv zeta;
    apply Z.mod_pos_bound; reflexivity.
Qed.

Lemma reduced_at_range zs a0 s0 k :
  0 <= fst (reduced_at zs a0 s0 k) < base /\
  0 <= snd (reduced_at zs a0 s0 k) < base.
Proof.
  unfold reduced_at.
  apply fold_step_reduced; cbn [fst snd]; apply Z.mod_pos_bound; reflexivity.
Qed.

Lemma modpair_reduced st :
  0 <= fst st < base -> 0 <= snd st < base -> modpair st = st.
Proof.
  intros. unfold modpair. destruct st as [a b]. cbn [fst snd] in *.
  rewrite !Z.mod_small by assumption. reflexivity.
Qed.

Lemma reduced_at_extend zs a0 s0 lo k :
  0 <= lo <= k -> k <= Zlength zs ->
  fold_left step (sublist lo k zs) (reduced_at zs a0 s0 lo) = reduced_at zs a0 s0 k.
Proof.
  intros. unfold reduced_at.
  rewrite (sublist_split 0 lo k) by lia. symmetry. apply fold_left_app.
Qed.

(** Reducing the accumulators over a stretch that starts from the reduced
    pair gives the reduced pair at the end of the stretch. *)
Lemma modpair_acc_reduced zs a0 s0 st lo k :
  0 <= lo <= k -> k <= Zlength zs ->
  modpair st = reduced_at zs a0 s0 lo ->
  modpair (acc zs st lo k) = reduced_at zs a0 s0 k.
Proof.
  intros. rewrite modpair_acc.
  match goal with H : modpair st = _ |- _ => rewrite H end.
  apply reduced_at_extend; assumption.
Qed.

(** ** The final pair is the one [update] computes *)

(** For a non-empty input it does not matter whether the starting pair is
    reduced, because the first step reduces. *)
Lemma fold_step_start l a b :
  l <> [] ->
  fold_left step l (a mod base, b mod base) = fold_left step l (a, b).
Proof.
  destruct l as [|x l]; [congruence|]. intros _. cbn [fold_left]. f_equal.
  rewrite step_mod. unfold step. cbn [fst snd]. cbv zeta. f_equal.
  rewrite Z.add_mod_idemp_r by apply base_nonzero. reflexivity.
Qed.

Theorem update_from_reduced adler zs :
  0 < Zlength zs ->
  let final := reduced_at zs (low16 adler) (high16 adler) (Zlength zs) in
  snd final * 65536 + fst final = update adler zs.
Proof.
  intros Hlen. cbv zeta. unfold reduced_at, update.
  rewrite sublist_same by lia.
  rewrite fold_step_start; [reflexivity|].
  intro E. rewrite E, Zlength_nil in Hlen. lia.
Qed.

(** ** The conditional subtraction used on short inputs *)

Lemma subtract_once x :
  0 <= x < 2 * base -> (if x >=? base then x - base else x) = x mod base.
Proof.
  intros. unfold base in *. rewrite Z.geb_leb.
  destruct (Z.leb_spec 65521 x).
  - apply (Z.mod_unique x 65521 1); lia.
  - symmetry. apply Z.mod_small. lia.
Qed.

(** ** The state at block boundaries

    The main loop reduces after each block of 5552 bytes.  [block_ok] says
    what the accumulators hold when [b] whole blocks are done.  Before the
    first block they hold the two halves of the incoming checksum, which
    need not be reduced.  After any block they hold the reduced pair. *)

Definition block_ok (adler : Z) (zs : list Z) (b : Z) (st : Z * Z) : Prop :=
  0 <= fst st <= 65535 /\ 0 <= snd st <= 65535 /\
  modpair st = reduced_at zs (low16 adler) (high16 adler) (5552 * b) /\
  (0 < b -> st = reduced_at zs (low16 adler) (high16 adler) (5552 * b)).

Lemma block_ok_init adler zs : block_ok adler zs 0 (low16 adler, high16 adler).
Proof.
  pose proof (low16_range adler). pose proof (high16_range adler).
  unfold block_ok. cbn [fst snd].
  (* the equation between the two pairs holds by computation *)
  repeat split; try lia.
Qed.

Lemma block_ok_step adler zs b st :
  block_ok adler zs b st -> 0 <= b -> 5552 * (b + 1) <= Zlength zs ->
  block_ok adler zs (b + 1) (modpair (acc zs st (5552 * b) (5552 * b + 5552))).
Proof.
  intros (H1 & H2 & H3 & H4) Hb Hn.
  assert (E : modpair (acc zs st (5552 * b) (5552 * b + 5552))
              = reduced_at zs (low16 adler) (high16 adler) (5552 * (b + 1))).
  { replace (5552 * (b + 1)) with (5552 * b + 5552) by lia.
    apply modpair_acc_reduced; [lia | lia | assumption]. }
  rewrite E.
  destruct (reduced_at_range zs (low16 adler) (high16 adler) (5552 * (b + 1)))
    as [R1 R2].
  unfold block_ok. unfold base in R1, R2. repeat split; try lia.
  apply modpair_reduced; unfold base; lia.
Qed.

(** Both accumulators stay within 64 bits during a block. *)
Lemma acc_block_bounds adler zs b st k :
  block_ok adler zs b st -> all_bytes zs -> 0 <= b ->
  5552 * b <= k -> k <= Zlength zs -> k - 5552 * b <= 5552 ->
  0 <= fst (acc zs st (5552 * b) k) <= Int64.max_unsigned /\
  0 <= snd (acc zs st (5552 * b) k) <= Int64.max_unsigned.
Proof.
  intros (H1 & H2 & _) Hbytes Hb Hlo Hk Hlen.
  pose proof (acc_bounds zs st (5552 * b) k Hbytes ltac:(lia) Hk Hlen H1 H2).
  rep_lia.
Qed.

(** When bytes remain after the last whole block, the reduced accumulators
    are the pair the specification has at the end. *)
Lemma tail_result adler zs b st :
  block_ok adler zs b st -> 0 <= b -> 5552 * b <= Zlength zs ->
  modpair (acc zs st (5552 * b) (Zlength zs))
  = reduced_at zs (low16 adler) (high16 adler) (Zlength zs).
Proof.
  intros (_ & _ & H3 & _) Hb Hn.
  apply modpair_acc_reduced; [lia | lia | assumption].
Qed.

(** When the input is a whole number of blocks, the accumulators already
    are that pair. *)
Lemma no_tail_result adler zs b st :
  block_ok adler zs b st -> 0 < b -> Zlength zs = 5552 * b ->
  st = reduced_at zs (low16 adler) (high16 adler) (Zlength zs).
Proof. intros (_ & _ & _ & H4) Hb E. rewrite E. apply H4. assumption. Qed.

Lemma reduced_at_bounds zs a0 s0 k :
  0 <= fst (reduced_at zs a0 s0 k) < 65536 /\
  0 <= snd (reduced_at zs a0 s0 k) < 65536.
Proof.
  destruct (reduced_at_range zs a0 s0 k) as [R1 R2]. unfold base in *. lia.
Qed.

(** ** Short inputs: fewer than 16 bytes, no blocks *)

Lemma short_bounds adler zs k :
  all_bytes zs -> 0 <= k <= Zlength zs -> k <= 15 ->
  0 <= fst (acc zs (low16 adler, high16 adler) 0 k) < 2 * base /\
  0 <= snd (acc zs (low16 adler, high16 adler) 0 k) <= Int64.max_unsigned.
Proof.
  intros Hbytes Hk Hshort.
  pose proof (low16_range adler). pose proof (high16_range adler).
  pose proof (raw_fold_bounds (sublist 0 k zs) (low16 adler, high16 adler)
                (all_bytes_sublist zs 0 k Hbytes)
                ltac:(cbn; lia) ltac:(cbn; lia)) as Hb.
  rewrite Zlength_sublist in Hb by lia. cbn [fst snd] in Hb.
  unfold acc, base. destruct Hb as [[B1 B2] [B3 B4]].
  assert (k * (low16 adler + 255 * k) <= 15 * (65536 + 255 * 15)) by nia.
  repeat split; try lia. rep_lia.
Qed.

Lemma short_result adler zs :
  0 < Zlength zs ->
  let p := modpair (acc zs (low16 adler, high16 adler) 0 (Zlength zs)) in
  snd p * 65536 + fst p = update adler zs.
Proof.
  intros Hlen. cbv zeta.
  pose proof (tail_result adler zs 0 (low16 adler, high16 adler)
                (block_ok_init adler zs) ltac:(lia) ltac:(lia)) as E.
  rewrite Z.mul_0_r in E. rewrite E.
  apply update_from_reduced. assumption.
Qed.

(** ** One byte: two conditional subtractions *)

Definition sub_once (y : Z) : Z := if y >=? base then y - base else y.

Lemma sub_once_range y : 0 <= y < 131056 -> 0 <= sub_once y < 65536.
Proof.
  intros. unfold sub_once, base. rewrite Z.geb_leb.
  destruct (Z.leb_spec 65521 y); lia.
Qed.

(** The second subtraction is exact only when the high half of the incoming
    checksum is already reduced.  For a genuine running checksum it is. *)
Lemma one_byte_update adler z0 :
  0 <= z0 -> high16 adler < base ->
  sub_once (high16 adler + (low16 adler + z0) mod base) * 65536
  + (low16 adler + z0) mod base
  = update adler [z0].
Proof.
  intros Hz Hhigh. pose proof (high16_range adler).
  pose proof (Z.mod_pos_bound (low16 adler + z0) base base_pos).
  unfold update. cbn [fold_left]. unfold step. cbn [fst snd]. cbv zeta.
  unfold sub_once. rewrite subtract_once by lia. reflexivity.
Qed.

Lemma mod_base_bounds x : 0 <= x mod base < 65536.
Proof.
  pose proof (Z.mod_pos_bound x base base_pos).
  assert (base = 65521) by reflexivity. lia.
Qed.
