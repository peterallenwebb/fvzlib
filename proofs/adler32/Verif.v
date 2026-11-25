(** * Adler-32: proofs of the C contracts (Layer 4)

    VST proofs that [adler32_z] of patched zlib 1.4 meets the contracts in
    [Spec.v].  The function proven is the real one, with no instrumentation,
    so these contracts attach to the code that ships in the patched tree. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Steps Buffer Spec.

(** ** Tactics *)

(* Close what [entailer!] leaves: arithmetic, equal integer values, and
   cells holding equal values. *)
Ltac fin1 :=
  first [ solve [lia]
        | solve [f_equal; lia]
        | solve [do 2 f_equal; lia]
        | solve [apply derives_refl'; do 3 f_equal; lia]
        | solve [cancel] ].
Ltac fin := repeat match goal with |- _ /\ _ => split end; try fin1.

(* Turn the machine-integer facts that a test leaves behind into facts
   about mathematical integers.  All the integers involved are in range. *)
Ltac norm_tests :=
  repeat match goal with
  | H : context [Int.sub (Int.repr ?a) (Int.repr ?b)] |- _ =>
      rewrite (sub_repr a b) in H
  | H : context [Int64.sub (Int64.repr ?a) (Int64.repr ?b)] |- _ =>
      rewrite (sub64_repr a b) in H
  | H : context [Int64.unsigned (Int64.repr ?x)] |- _ =>
      rewrite (Int64.unsigned_repr x) in H by rep_lia
  | H : context [Int.unsigned (Int.repr ?x)] |- _ =>
      rewrite (Int.unsigned_repr x) in H by rep_lia
  | H : Int64.repr ?x = Int64.zero |- _ =>
      change Int64.zero with (Int64.repr 0) in H;
      apply repr_inj_unsigned64 in H; [ | rep_lia | rep_lia ]
  | H : Int64.repr ?x <> Int64.zero |- _ =>
      assert (x <> 0) by (let E := fresh in intro E; apply H; rewrite E; reflexivity);
      clear H
  | H : Int.repr ?x = Int.zero |- _ =>
      change Int.zero with (Int.repr 0) in H;
      apply repr_inj_unsigned in H; [ | rep_lia | rep_lia ]
  | H : Int.repr ?x <> Int.zero |- _ =>
      assert (x <> 0) by (let E := fresh in intro E; apply H; rewrite E; reflexivity);
      clear H
  | H : Int64.repr ?x <> Int64.repr ?y |- _ =>
      assert (x <> y) by (let E := fresh in intro E; apply H; rewrite E; reflexivity);
      clear H
  | H : Int64.eq (Int64.repr ?x) (Int64.repr ?y) = true |- _ =>
      apply Int64.same_if_eq in H; apply repr_inj_unsigned64 in H;
      [ | rep_lia | rep_lia ]
  end.

(* Read one byte by index, then expose the byte that was read. *)
Ltac load_byte :=
  forward;
  [ entailer!; apply tc_Vubyte
  | rewrite Znth_map by list_solve ].

(* Split the buffer at position i, and put it back together. *)
Ltac split_at sh bs base i :=
  sep_apply (@split_buffer CompSpecs sh bs base i ltac:(lia));
  unfold suffix_at; Intros.
Ltac merge_at sh bs base i :=
  sep_apply (@merge_parts CompSpecs sh bs base i ltac:(lia) ltac:(assumption)).

(* After a byte has been read and added in, restate the two accumulators
   as the model's accumulators one byte further on. *)
Ltac track bs :=
  match goal with
  | |- context [Int64.add (Int64.repr (fst (acc (bytes_of bs) ?st ?lo ?k)))
                          (Int64.repr (Int.unsigned (Int.repr (Byte.unsigned ?b))))] =>
      rewrite (acc_fst_step (bytes_of bs) st lo k b
                 ltac:(lia) ltac:(rewrite Zlength_bytes_of; lia)
                 ltac:(rewrite byte_at by lia; f_equal; lia));
      rewrite (acc_snd_step (bytes_of bs) st lo k
                 ltac:(lia) ltac:(rewrite Zlength_bytes_of; lia))
  end.

(* One unrolled step of the checksum. *)
Ltac do1 bs := load_byte; forward; forward; track bs.

(** ** The null buffer *)

Lemma body_adler32_z_null :
  semax_body Vprog [] f_adler32_z adler32_z_null_spec.
Proof.
  start_function.
  forward. forward.
  forward_if (PROP (False) LOCAL () SEP ()).
  - forward. Exists 1. entailer!.
    apply Adler32Facts.adler32_initial_value. reflexivity.
  - (* the buffer is null, so the other branch cannot be taken *)
    exfalso. match goal with H : ?x <> ?x |- _ => apply H; reflexivity end.
Qed.

(** ** A non-empty buffer *)

Lemma body_adler32_z_buffer :
  semax_body Vprog [] f_adler32_z adler32_z_buffer_spec.
Proof.
  start_function.
  pose proof (bytes_of_all_bytes bs) as Hbytes.
  pose proof (Zlength_bytes_of bs) as Hlen.
  pose proof (low16_range adler) as Hlow.
  pose proof (high16_range adler) as Hhigh.
  forward. forward.
  rewrite (Int.signed_repr 65535), (Int.unsigned_repr 16) by rep_lia.
  rewrite shr_high16, and_low16 by lia.
  assert_PROP (isptr buf) as Hptr by entailer!.
  forward_if
    (PROP ()
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
  { (* buf == Z_NULL cannot happen: the buffer is a real one *)
    exfalso. destruct buf; try contradiction.
    unfold nullval in *; simpl in *; discriminate. }
  { forward. entailer!. }
  (* ---- one byte ---- *)
  forward_if
    (PROP (Zlength bs <> 1)
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
  { norm_tests.
    load_byte. forward.
    rewrite byte_val, add64_repr.
    pose proof (Byte.unsigned_range_2 (Znth 0 bs)) as Hz.
    set (z0 := Byte.unsigned (Znth 0 bs)) in *.
    pose proof (Z.mod_pos_bound (low16 adler + z0) base base_pos) as Ha1.
    forward_if
      (PROP ()
       LOCAL (temp _adler (Vlong (Int64.repr ((low16 adler + z0) mod base)));
              temp _sum2 (Vlong (Int64.repr (high16 adler)));
              temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
    { norm_tests. forward.
      assert (E : (low16 adler + z0) mod base = low16 adler + z0 - 65521)
        by (unfold base; symmetry; apply (Z.mod_unique _ 65521 1); rep_lia).
      rewrite E. entailer!; fin. }
    { norm_tests. forward.
      assert (E : (low16 adler + z0) mod base = low16 adler + z0)
        by (apply Z.mod_small; unfold base; rep_lia).
      rewrite E. entailer!; fin. }
    forward. rewrite add64_repr.
    set (a1 := (low16 adler + z0) mod base) in *.
    unfold base in Ha1.
    forward_if
      (PROP ()
       LOCAL (temp _adler (Vlong (Int64.repr a1));
              temp _sum2 (Vlong (Int64.repr (sub_once (high16 adler + a1))));
              temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
    { norm_tests. forward.
      assert (E : sub_once (high16 adler + a1) = high16 adler + a1 - 65521)
        by (unfold sub_once, base; rewrite Z.geb_leb;
            destruct (Z.leb_spec 65521 (high16 adler + a1)); lia).
      rewrite E. entailer!; fin. }
    { norm_tests. forward.
      assert (E : sub_once (high16 adler + a1) = high16 adler + a1)
        by (unfold sub_once, base; rewrite Z.geb_leb;
            destruct (Z.leb_spec 65521 (high16 adler + a1)); lia).
      rewrite E. entailer!; fin. }
    pose proof (sub_once_range (high16 adler + a1) ltac:(lia)) as Hy.
    forward.
    Exists (sub_once (high16 adler + a1) * 65536 + a1).
    rewrite pack_or by lia.
    entailer!.
    apply spec_from_update. intros [Hh | Hn]; [|lia].
    rewrite (bytes_of_one bs) by assumption. fold z0.
    apply one_byte_update; [rep_lia | assumption]. }
  { norm_tests. forward. entailer!. }
  Intros.
  (* ---- fewer than 16 bytes ---- *)
  forward_if
    (PROP (16 <= Zlength bs)
     LOCAL (temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
  { norm_tests.
    forward_loop
      (EX j : Z,
         PROP (0 <= j <= Zlength bs)
         LOCAL (temp _adler (Vlong (Int64.repr
                  (fst (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _sum2 (Vlong (Int64.repr
                  (snd (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _buf (offset_val j buf);
                temp _len (Vlong (Int64.repr (Zlength bs - j))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf))
      break:
      (PROP ()
       LOCAL (temp _adler (Vlong (Int64.repr
                (fst (acc (bytes_of bs) (low16 adler, high16 adler) 0
                          (Zlength bs)))));
              temp _sum2 (Vlong (Int64.repr
                (snd (acc (bytes_of bs) (low16 adler, high16 adler) 0
                          (Zlength bs))))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
    - Exists 0. rewrite acc_start. entailer!; fin.
    - Intros j.
      forward. forward.
      forward_if
        (PROP (Zlength bs - j <> 0)
         LOCAL (temp _adler (Vlong (Int64.repr
                  (fst (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _sum2 (Vlong (Int64.repr
                  (snd (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _buf (offset_val j buf);
                temp _len (Vlong (Int64.repr (Zlength bs - j - 1))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
      + norm_tests. forward. entailer!; fin.
      + norm_tests. assert (j = Zlength bs) by lia. subst j.
        forward. entailer!.
      + Intros. forward. forward.
        split_at sh bs buf j.
        assert (Hfa := @suffix_head_address CompSpecs bs buf j
                         ltac:(lia) ltac:(assumption)).
        do1 bs.
        merge_at sh bs buf j.
        Exists (j + 1). entailer!; fin.
    - (* reduce, pack, and return *)
      destruct (short_bounds adler (bytes_of bs) (Zlength bs) Hbytes
                  ltac:(lia) ltac:(lia)) as [Bf Bs].
      unfold base in Bf.
      set (X := fst (acc (bytes_of bs) (low16 adler, high16 adler) 0
                         (Zlength bs))) in *.
      set (S := snd (acc (bytes_of bs) (low16 adler, high16 adler) 0
                         (Zlength bs))) in *.
      forward_if
        (PROP ()
         LOCAL (temp _adler (Vlong (Int64.repr (X mod base)));
                temp _sum2 (Vlong (Int64.repr S)))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
      { norm_tests. forward.
        assert (E : X mod base = X - 65521)
          by (unfold base; symmetry; apply (Z.mod_unique _ 65521 1); lia).
        rewrite E. entailer!; fin. }
      { norm_tests. forward.
        assert (E : X mod base = X) by (apply Z.mod_small; unfold base; lia).
        rewrite E. entailer!; fin. }
      forward.
      rewrite (Int.unsigned_repr 65521) by rep_lia. rewrite modu_base by lia.
      forward.
      Exists (S mod base * 65536 + X mod base).
      rewrite pack_or by apply mod_base_bounds.
      pose proof (mod_base_bounds X). pose proof (mod_base_bounds S).
      entailer!.
      apply spec_from_update. intros _.
      pose proof (short_result adler (bytes_of bs) ltac:(lia)) as Rr.
      cbv zeta in Rr. unfold modpair in Rr. cbn [fst snd] in Rr.
      rewrite Hlen in Rr. exact Rr. }
  { norm_tests. forward. entailer!. }
  Intros.
  (* ---- the main loop, over blocks of 5552 bytes ---- *)
  forward_loop
    (EX b : Z, EX st : Z * Z,
       PROP (0 <= b; 5552 * b <= Zlength bs;
             block_ok adler (bytes_of bs) b st)
       LOCAL (temp _adler (Vlong (Int64.repr (fst st)));
              temp _sum2 (Vlong (Int64.repr (snd st)));
              temp _buf (offset_val (5552 * b) buf);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf))
    break:
    (EX b : Z, EX st : Z * Z,
       PROP (0 <= b; 5552 * b <= Zlength bs; Zlength bs - 5552 * b < 5552;
             block_ok adler (bytes_of bs) b st)
       LOCAL (temp _adler (Vlong (Int64.repr (fst st)));
              temp _sum2 (Vlong (Int64.repr (snd st)));
              temp _buf (offset_val (5552 * b) buf);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
  - Exists 0 (low16 adler, high16 adler).
    pose proof (block_ok_init adler (bytes_of bs)).
    entailer!; fin.
  - Intros b st.
    forward_if
      (PROP (5552 <= Zlength bs - 5552 * b)
       LOCAL (temp _adler (Vlong (Int64.repr (fst st)));
              temp _sum2 (Vlong (Int64.repr (snd st)));
              temp _buf (offset_val (5552 * b) buf);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
    + norm_tests. forward. entailer!; fin.
    + norm_tests. forward. Exists b st. entailer!; fin.
    + Intros. forward. forward.
      (* the inner loop: 347 iterations of 16 bytes each *)
      forward_loop
        (EX m : Z,
           PROP (0 <= m < 347)
           LOCAL (temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 5552)));
                  temp _n (Vint (Int.repr (347 - m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf))
        continue:
        (EX m : Z,
           PROP (0 <= m < 347)
           LOCAL (temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b)
                              (5552 * b + 16 * (m + 1))))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b)
                              (5552 * b + 16 * (m + 1))))));
                  temp _buf (offset_val (5552 * b + 16 * (m + 1)) buf);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 5552)));
                  temp _n (Vint (Int.repr (347 - m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf))
        break:
        (PROP ()
         LOCAL (temp _adler (Vlong (Int64.repr
                  (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 5552)))));
                temp _sum2 (Vlong (Int64.repr
                  (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 5552)))));
                temp _buf (offset_val (5552 * (b + 1)) buf);
                temp _len (Vlong (Int64.repr (Zlength bs - 5552 * (b + 1)))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
      * Exists 0. rewrite inner_count.
        rewrite Z.mul_0_r, Z.add_0_r, acc_start. entailer!; fin.
      * Intros m.
        split_at sh bs buf (5552 * b + 16 * m).
        do 16 (do1 bs).
        forward.
        merge_at sh bs buf (5552 * b + 16 * m).
        match goal with
        | |- context [acc (bytes_of bs) st (5552 * b) ?k] =>
            replace k with (5552 * b + 16 * (m + 1)) by lia
        end.
        Exists m. entailer!; fin.
      * (* the loop test, which counts n down *)
        Intros m.
        forward. forward.
        forward_if.
        -- norm_tests. forward. norm_tests.
           Exists (m + 1). entailer!; fin.
        -- norm_tests. forward. norm_tests.
           assert (m = 346) by lia. subst m.
           replace (5552 * b + 16 * (346 + 1)) with (5552 * b + 5552) by lia.
           entailer!; fin.
      * (* a whole block is done: reduce both accumulators *)
        match goal with H : block_ok _ _ _ _ |- _ => rename H into Hok end.
        destruct (acc_block_bounds adler (bytes_of bs) b st (5552 * b + 5552)
                    Hok Hbytes ltac:(lia) ltac:(lia)
                    ltac:(rewrite Zlength_bytes_of; lia) ltac:(lia))
          as [Bf Bs].
        forward. forward.
        rewrite (Int.unsigned_repr 65521) by rep_lia.
        rewrite !modu_base by lia.
        pose proof (block_ok_step adler (bytes_of bs) b st Hok ltac:(lia)
                      ltac:(rewrite Zlength_bytes_of; lia)) as Hnext.
        Exists (b + 1)
               (modpair (acc (bytes_of bs) st (5552 * b) (5552 * b + 5552))).
        cbn [modpair fst snd].
        entailer!; fin.
  - (* ---- after the main loop: fewer than 5552 bytes remain ---- *)
    Intros b st.
    match goal with H : block_ok _ _ _ _ |- _ => rename H into Hok end.
    forward_if
      (PROP ()
       LOCAL (temp _adler (Vlong (Int64.repr
                (fst (reduced_at (bytes_of bs) (low16 adler) (high16 adler)
                                 (Zlength bs)))));
              temp _sum2 (Vlong (Int64.repr
                (snd (reduced_at (bytes_of bs) (low16 adler) (high16 adler)
                                 (Zlength bs))))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
    + (* some bytes remain *)
      norm_tests.
      (* sixteen bytes at a time *)
      forward_loop
        (EX m : Z,
           PROP (0 <= m; 16 * m <= Zlength bs - 5552 * b)
           LOCAL (temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr
                               (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf))
        break:
        (EX m : Z,
           PROP (0 <= m; 16 * m <= Zlength bs - 5552 * b;
                 Zlength bs - 5552 * b - 16 * m < 16)
           LOCAL (temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr
                               (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
      * Exists 0. rewrite Z.mul_0_r, Z.add_0_r, acc_start. entailer!; fin.
      * Intros m.
        forward_if
          (PROP (16 <= Zlength bs - 5552 * b - 16 * m)
           LOCAL (temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr
                               (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
        -- norm_tests. forward. entailer!; fin.
        -- norm_tests. forward. Exists m. entailer!; fin.
        -- Intros. forward.
           split_at sh bs buf (5552 * b + 16 * m).
           do 16 (do1 bs).
           forward.
           merge_at sh bs buf (5552 * b + 16 * m).
           match goal with
           | |- context [acc (bytes_of bs) st (5552 * b) ?k] =>
               replace k with (5552 * b + 16 * (m + 1)) by lia
           end.
           Exists (m + 1). entailer!; fin.
      * (* one byte at a time *)
        Intros m.
        forward_loop
          (EX j : Z,
             PROP (0 <= j <= Zlength bs - 5552 * b - 16 * m)
             LOCAL (temp _adler (Vlong (Int64.repr
                      (fst (acc (bytes_of bs) st (5552 * b)
                                (5552 * b + 16 * m + j)))));
                    temp _sum2 (Vlong (Int64.repr
                      (snd (acc (bytes_of bs) st (5552 * b)
                                (5552 * b + 16 * m + j)))));
                    temp _buf (offset_val (5552 * b + 16 * m + j) buf);
                    temp _len (Vlong (Int64.repr
                                 (Zlength bs - 5552 * b - 16 * m - j))))
             SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf))
          break:
          (PROP ()
           LOCAL (temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (Zlength bs)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (Zlength bs))))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
        -- Exists 0. rewrite Z.add_0_r. entailer!; fin.
        -- Intros j. forward. forward.
           forward_if
             (PROP (Zlength bs - 5552 * b - 16 * m - j <> 0)
              LOCAL (temp _adler (Vlong (Int64.repr
                       (fst (acc (bytes_of bs) st (5552 * b)
                                 (5552 * b + 16 * m + j)))));
                     temp _sum2 (Vlong (Int64.repr
                       (snd (acc (bytes_of bs) st (5552 * b)
                                 (5552 * b + 16 * m + j)))));
                     temp _buf (offset_val (5552 * b + 16 * m + j) buf);
                     temp _len (Vlong (Int64.repr
                                  (Zlength bs - 5552 * b - 16 * m - j - 1))))
              SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)).
           ++ norm_tests. forward. entailer!; fin.
           ++ norm_tests. forward.
              replace (5552 * b + 16 * m + j) with (Zlength bs) by lia.
              entailer!.
           ++ Intros. forward. forward.
              split_at sh bs buf (5552 * b + 16 * m + j).
              assert (Hfa := @suffix_head_address CompSpecs bs buf
                               (5552 * b + 16 * m + j)
                               ltac:(lia) ltac:(assumption)).
              do1 bs.
              merge_at sh bs buf (5552 * b + 16 * m + j).
              replace (5552 * b + 16 * m + j + 1)
                with (5552 * b + 16 * m + (j + 1)) by lia.
              Exists (j + 1). entailer!; fin.
        -- (* reduce both accumulators *)
           destruct (acc_block_bounds adler (bytes_of bs) b st (Zlength bs)
                       Hok Hbytes ltac:(lia) ltac:(lia)
                       ltac:(rewrite Zlength_bytes_of; lia) ltac:(lia))
             as [Bf Bs].
           forward. forward.
           rewrite (Int.unsigned_repr 65521) by rep_lia.
           rewrite !modu_base by lia.
           pose proof (tail_result adler (bytes_of bs) b st Hok ltac:(lia)
                         ltac:(rewrite Zlength_bytes_of; lia)) as Ht.
           rewrite Hlen in Ht. rewrite <- Ht. cbn [modpair fst snd].
           entailer!.
    + (* no bytes remain: the input was a whole number of blocks *)
      norm_tests.
      pose proof (no_tail_result adler (bytes_of bs) b st Hok ltac:(lia)
                    ltac:(rewrite Zlength_bytes_of; lia)) as Hn.
      rewrite Hlen in Hn. forward. rewrite <- Hn. entailer!.
    + (* pack the two halves and return *)
      destruct (reduced_at_bounds (bytes_of bs) (low16 adler) (high16 adler)
                  (Zlength bs)) as [Rf Rs].
      set (F := reduced_at (bytes_of bs) (low16 adler) (high16 adler)
                           (Zlength bs)) in *.
      forward.
      Exists (snd F * 65536 + fst F).
      rewrite pack_or by lia.
      entailer!.
      apply spec_from_update. intros _.
      pose proof (update_from_reduced adler (bytes_of bs) ltac:(lia)) as U.
      cbv zeta in U. rewrite Hlen in U. exact U.
Qed.
