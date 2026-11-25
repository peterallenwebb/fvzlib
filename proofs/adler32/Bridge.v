(** * Adler-32: machine integers and mathematical integers

    The C code computes with 64-bit unsigned integers.  The specification
    is stated over mathematical integers.  These lemmas say what each
    machine operation the code uses does, in terms of mathematical
    integers, when the values involved are in range. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.

Local Open Scope Z_scope.

(** The bytes of a buffer, as mathematical integers. *)
Definition bytes_of (bs : list byte) : list Z := map Byte.unsigned bs.

Lemma bytes_of_all_bytes bs : all_bytes (bytes_of bs).
Proof.
  unfold all_bytes, bytes_of. induction bs as [|b bs IH]; constructor; auto.
  unfold is_byte. pose proof (Byte.unsigned_range b) as H.
  change Byte.modulus with 256 in H. lia.
Qed.

Lemma Zlength_bytes_of bs : Zlength (bytes_of bs) = Zlength bs.
Proof. unfold bytes_of. apply Zlength_map. Qed.

(** The byte read at offset [j] past position [i] is the byte at [i + j]. *)
Lemma byte_at bs i j :
  0 <= i -> 0 <= j -> i + j < Zlength bs ->
  Byte.unsigned (Znth j (sublist i (Zlength bs) bs)) = Znth (i + j) (bytes_of bs).
Proof.
  intros. unfold bytes_of.
  rewrite Znth_sublist by lia. rewrite Znth_map by lia.
  do 2 f_equal. lia.
Qed.

(** A byte widened to 64 bits. *)
Lemma byte_val b :
  Int64.repr (Int.unsigned (Int.repr (Byte.unsigned b)))
  = Int64.repr (Byte.unsigned b).
Proof.
  pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

(** [adler & 0xffff] *)
Lemma and_low16 x :
  0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.repr x) (Int64.repr 65535) = Int64.repr (low16 x).
Proof.
  intros. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  f_equal. unfold low16. change 65535 with (Z.ones 16).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

(** [(adler >> 16) & 0xffff] *)
Lemma shr_high16 x :
  0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.shru (Int64.repr x) (Int64.repr 16)) (Int64.repr 65535)
  = Int64.repr (high16 x).
Proof.
  intros. rewrite Int64.shru_div_two_p.
  rewrite !Int64.unsigned_repr by rep_lia. change (two_p 16) with 65536.
  assert (0 <= x / 65536 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia|].
    assert (x / 65536 <= x) by (apply Z.div_le_upper_bound; lia). lia. }
  rewrite and_low16 by assumption. reflexivity.
Qed.

(** [x % BASE] *)
Lemma modu_base x :
  0 <= x <= Int64.max_unsigned ->
  Int64.modu (Int64.repr x) (Int64.repr 65521) = Int64.repr (x mod base).
Proof.
  intros. unfold Int64.modu. rewrite !Int64.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma lor_pack a s :
  0 <= a < 65536 -> 0 <= s -> Z.lor a (s * 65536) = s * 65536 + a.
Proof.
  intros Ha Hs.
  assert (Hland : Z.land a (s * 65536) = 0).
  { change 65536 with (2 ^ 16). rewrite <- Z.shiftl_mul_pow2 by lia.
    apply Z.bits_inj'. intros n Hn.
    rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 16).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - assert (Z.log2 a < n).
      { destruct (Z.eq_dec a 0) as [->|]; [simpl; lia|].
        apply Z.log2_lt_pow2; [lia|].
        assert (2 ^ 16 <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
        change (2 ^ 16) with 65536 in *. lia. }
      rewrite (Z.bits_above_log2 a n) by lia. reflexivity. }
  rewrite Z.add_comm, (Z.add_nocarry_lxor a (s * 65536) Hland).
  symmetry. apply Z.lxor_lor. exact Hland.
Qed.

(** [adler | (sum2 << 16)] *)
Lemma pack_or a s :
  0 <= a < 65536 -> 0 <= s < 65536 ->
  Int64.or (Int64.repr a) (Int64.shl (Int64.repr s) (Int64.repr 16))
  = Int64.repr (s * 65536 + a).
Proof.
  intros. rewrite Int64.shl_mul_two_p.
  rewrite (Int64.unsigned_repr 16) by rep_lia. change (two_p 16) with 65536.
  rewrite mul64_repr. unfold Int64.or.
  rewrite !Int64.unsigned_repr by rep_lia.
  rewrite lor_pack by lia. reflexivity.
Qed.

(** The packed pair fits in 32 bits. *)
Lemma pack_range a s :
  0 <= a < 65536 -> 0 <= s < 65536 -> 0 <= s * 65536 + a < 4294967296.
Proof. intros. lia. Qed.

(** A buffer of one byte. *)
Lemma bytes_of_one bs :
  Zlength bs = 1 -> bytes_of bs = [Byte.unsigned (Znth 0 bs)].
Proof.
  intros H. destruct bs as [|b [|c bs]].
  - rewrite Zlength_nil in H. lia.
  - reflexivity.
  - rewrite !Zlength_cons in H. pose proof (Zlength_nonneg bs). lia.
Qed.

(** The inner loop of the block loop runs 5552 / 16 = 347 times. *)
Lemma inner_count : Int.divs (Int.repr 5552) (Int.repr 16) = Int.repr 347.
Proof. unfold Int.divs. rewrite !Int.signed_repr by rep_lia. reflexivity. Qed.
