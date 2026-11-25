(** * Adler-32: a buffer of length zero

    The manual lets a caller pass a buffer that is not null with a length of
    zero.  [Spec.v] does not cover that call: its buffer contract needs at
    least one byte.  This file adds the missing case for [adler32_z] and
    [adler32].

    A pointer with no bytes behind it still has to be a real pointer, because
    the code compares it with null, and C gives that comparison a meaning
    only for null and for pointers into, or one past the end of, an object.
    Following the Layer 3 design, the contract asks for a position in a
    non-empty array that the caller owns.  The position may be anywhere from
    the first byte to one past the last byte.  Nothing in the array is read,
    and the array is returned unchanged.

    The result is the checksum that was passed in, whenever that is a
    genuine running checksum.  That is what the Layer 2 specification says
    for no bytes. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Spec Verif.

(** ** Contracts *)

(** [before] and [after] are the bytes of the caller's array on either side
    of the position passed.  Either may be empty, but not both. *)
Definition adler32_z_empty_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, sh : share, before : list byte, after : list byte, arr : val
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength (before ++ after))
    PARAMS (Vlong (Int64.repr adler); offset_val (Zlength before) arr;
            Vlong (Int64.repr 0))
    SEP (data_at sh (tarray tuchar (Zlength (before ++ after)))
                 (map Vubyte (before ++ after)) arr)
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler (Some []) r; 0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar (Zlength (before ++ after)))
                 (map Vubyte (before ++ after)) arr).

Definition adler32_empty_spec : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, sh : share, before : list byte, after : list byte, arr : val
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength (before ++ after))
    PARAMS (Vlong (Int64.repr adler); offset_val (Zlength before) arr;
            Vint (Int.repr 0))
    SEP (data_at sh (tarray tuchar (Zlength (before ++ after)))
                 (map Vubyte (before ++ after)) arr)
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler (Some []) r; 0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar (Zlength (before ++ after)))
                 (map Vubyte (before ++ after)) arr).

(** ** Supporting facts *)

(** For no bytes the code returns the two halves of the incoming value,
    each reduced.  A genuine running checksum already has reduced halves,
    so it comes back unchanged. *)
Lemma empty_result_spec adler :
  adler32_spec adler (Some [])
    (high16 adler mod base * 65536 + low16 adler mod base).
Proof.
  intros _ earlier [Hearlier ->]. rewrite app_nil_r. split; [assumption |].
  rewrite low16_adler32, high16_adler32.
  rewrite !Z.mod_small by (apply s1_range || apply s2_range).
  reflexivity.
Qed.

(** Every position in a non-empty array, including the one just past its
    end, may be compared with null. *)
Lemma array_position_comparable sh (bs : list byte) (arr : val) (k : Z) :
  readable_share sh -> 0 < Zlength bs -> 0 <= k <= Zlength bs ->
  data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) arr
  |-- weak_valid_pointer (offset_val k arr).
Proof.
  intros Hsh Hn Hk.
  sep_apply (data_at_memory_block sh (tarray tuchar (Zlength bs))
               (map Vubyte bs) arr).
  simpl sizeof. rewrite Z.max_r by lia.
  apply memory_block_weak_valid_pointer; [lia | lia |].
  apply readable_nonidentity. assumption.
Qed.

(** A pointer that may be compared with null passes VST's check on the
    comparison. *)
Transparent denote_tc_test_eq.
Lemma comparable_with_null (p : val) :
  isptr p ->
  weak_valid_pointer p |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hp. destruct p; try contradiction.
  unfold denote_tc_test_eq. simpl.
  apply andp_right; [apply prop_right; reflexivity | apply derives_refl].
Qed.
Opaque denote_tc_test_eq.

(** ** Proofs *)

Lemma body_adler32_z_empty :
  semax_body Vprog [adler32_z_empty_spec] f_adler32_z adler32_z_empty_spec.
Proof.
  start_function.
  pose proof (low16_range adler) as Hlow.
  pose proof (high16_range adler) as Hhigh.
  pose proof (Zlength_nonneg before) as Hbefore.
  pose proof (Zlength_nonneg after) as Hafter.
  assert (Hk : 0 <= Zlength before <= Zlength (before ++ after))
    by (rewrite Zlength_app; lia).
  set (bs := before ++ after) in *.
  set (k := Zlength before) in *.
  forward. forward.
  rewrite (Int.signed_repr 65535), (Int.unsigned_repr 16) by rep_lia.
  rewrite shr_high16, and_low16 by lia.
  assert_PROP (isptr arr) as Hptr by entailer!.
  forward_if
    (PROP ()
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf (offset_val k arr); temp _len (Vlong (Int64.repr 0)))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) arr)).
  { (* the comparison with null is one C defines *)
    sep_apply (array_position_comparable sh bs arr k SH H0 Hk).
    apply comparable_with_null. destruct arr; try contradiction. exact I. }
  { (* buf == Z_NULL cannot happen: the pointer is a real one *)
    exfalso. destruct arr; try contradiction.
    unfold nullval in *; simpl in *; discriminate. }
  { forward. entailer!. }
  (* ---- the length is not one ---- *)
  forward_if
    (PROP ()
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf (offset_val k arr); temp _len (Vlong (Int64.repr 0)))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) arr)).
  { exfalso. norm_tests. lia. }
  { forward. entailer!. }
  (* ---- fewer than 16 bytes: the branch taken ---- *)
  forward_if (PROP (False) LOCAL () SEP ()).
  2: { exfalso. norm_tests. lia. }
  forward_loop
    (PROP ()
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf (offset_val k arr); temp _len (Vlong (Int64.repr 0)))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) arr))
    break:
    (PROP ()
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) arr)).
  - entailer!.
  - (* the loop test fails at once, so no byte is read *)
    forward. forward.
    forward_if (PROP (False) LOCAL () SEP ()).
    + exfalso. norm_tests. lia.
    + forward. entailer!.
  - (* reduce, pack, and return *)
    unfold base in *.
    forward_if
      (PROP ()
       LOCAL (temp _adler (Vlong (Int64.repr (low16 adler mod base)));
              temp _sum2 (Vlong (Int64.repr (high16 adler))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) arr)).
    { norm_tests. forward.
      assert (E : low16 adler mod base = low16 adler - 65521)
        by (unfold base; symmetry; apply (Z.mod_unique _ 65521 1); lia).
      rewrite E. entailer!; fin. }
    { norm_tests. forward.
      assert (E : low16 adler mod base = low16 adler)
        by (apply Z.mod_small; unfold base; lia).
      rewrite E. entailer!; fin. }
    forward.
    rewrite (Int.unsigned_repr 65521) by rep_lia. rewrite modu_base by rep_lia.
    forward.
    Exists (high16 adler mod base * 65536 + low16 adler mod base).
    rewrite pack_or by apply mod_base_bounds.
    pose proof (mod_base_bounds (low16 adler)).
    pose proof (mod_base_bounds (high16 adler)).
    entailer!.
    apply empty_result_spec.
Qed.

Lemma body_adler32_empty :
  semax_body Vprog [adler32_z_empty_spec; adler32_empty_spec]
             f_adler32 adler32_empty_spec.
Proof.
  start_function.
  forward_call (adler, sh, before, after, arr).
  Intros r. forward. Exists r. entailer!.
Qed.

Print Assumptions body_adler32_z_empty.
Print Assumptions body_adler32_empty.
