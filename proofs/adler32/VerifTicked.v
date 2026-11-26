(** * Adler-32: proofs for [adler32_z] with ticks (Layer 4)

    VST proofs about [f_adler32_z_ticked], the function of patched zlib 1.4
    with a counter added.  Each proves one contract that covers memory
    safety, the value returned, and the number of ticks spent, for one
    kind of buffer argument: null, not empty, and not null with a length
    of zero.  [CostContractProof.v] puts the three together.

    The proof for a buffer that is not empty follows the proof of the
    plain function in [Verif.v] step by step.  It differs in three ways:
    each loop invariant has one more clause, saying what the counter
    holds; each tick is one more proof step; and the value returned comes
    with a second number, the ticks used.  We do not yet have a way to run
    one proof script against both forms of a function, so the steps are
    repeated here. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.lib Require Import Ticks TickLogic.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Steps
  Buffer Spec Contract Ticked CostContract EmptyBuffer.
(* Last, so that its tactics are the ones in force. *)
From fvzlib.proofs.adler32 Require Import Verif.

(** ** Contracts, one for each kind of buffer argument *)

Definition adler32_z_null_ticked_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, len : Z, gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned;
          1 <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); nullval; Vlong (Int64.repr len))
    GLOBALS (gv)
    SEP (ticks gv t)
  POST [ tulong ]
    EX r : Z, EX used : Z,
    PROP (adler32_spec adler None r; 0 <= used <= 1)
    RETURN (Vlong (Int64.repr r))
    SEP (ticks gv (t - used)).

Definition adler32_z_buffer_ticked_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, sh : share, bs : list byte, buf : val, gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength bs <= Int64.max_unsigned;
          buffer_cost (Zlength bs) <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); buf; Vlong (Int64.repr (Zlength bs)))
    GLOBALS (gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
         ticks gv t)
  POST [ tulong ]
    EX r : Z, EX used : Z,
    PROP (adler32_spec adler (Some (bytes_of bs)) r; 0 <= r < 4294967296;
          0 <= used <= buffer_cost (Zlength bs))
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
         ticks gv (t - used)).

Definition adler32_z_empty_ticked_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, sh : share, before : list val, after : list val, arr : val,
       gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; sepalg.nonidentity sh;
          0 < Zlength (before ++ after);
          buffer_cost 0 <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); offset_val (Zlength before) arr;
            Vlong (Int64.repr 0))
    GLOBALS (gv)
    SEP (data_at sh (tarray tuchar (Zlength (before ++ after)))
                 (before ++ after) arr;
         ticks gv t)
  POST [ tulong ]
    EX r : Z, EX used : Z,
    PROP (adler32_spec adler (Some []) r; 0 <= r < 4294967296;
          0 <= used <= buffer_cost 0)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar (Zlength (before ++ after)))
                 (before ++ after) arr;
         ticks gv (t - used)).

(** The cell that holds the counter, as the proofs below see it. *)
Local Abbreviation tk gv x :=
  (data_at Ews tulong (Vlong (Int64.repr x)) (gv _fvz_ticks)).

(** ** Arithmetic behind the cost bound

    5552 is 16 times 347, so a block of 5552 bytes takes 347 iterations of
    the inner loop, and with the test of the outer loop costs 348 ticks. *)

Lemma div_facts n b m :
  0 <= b -> 0 <= m -> 5552 * b + 16 * m <= n ->
  b <= n / 5552 /\ 347 * b + m <= n / 16.
Proof. intros. split; apply Z.div_le_lower_bound; lia. Qed.

Lemma cost_tail n b m :
  0 <= b -> 5552 * b <= n -> n - 5552 * b < 5552 ->
  0 <= m -> 16 * m <= n - 5552 * b -> n - 5552 * b - 16 * m < 16 ->
  4 + 348 * b + m + (n - 5552 * b - 16 * m) <= n / 5552 + n / 16 + 19.
Proof.
  intros.
  assert (n / 5552 = b)
    by (symmetry; apply (Z.div_unique n 5552 b (n - 5552 * b)); lia).
  assert (n / 16 = 347 * b + m)
    by (symmetry;
        apply (Z.div_unique n 16 (347 * b + m) (n - 5552 * b - 16 * m)); lia).
  lia.
Qed.

Lemma cost_whole_blocks n b :
  0 <= b -> n = 5552 * b -> 2 + 348 * b <= n / 5552 + n / 16 + 19.
Proof.
  intros.
  assert (n / 5552 = b) by (symmetry; apply (Z.div_unique n 5552 b 0); lia).
  assert (n / 16 = 347 * b)
    by (symmetry; apply (Z.div_unique n 16 (347 * b) 0); lia).
  lia.
Qed.

(** ** A buffer that is not empty *)

Lemma body_adler32_z_buffer_ticked :
  semax_body Vprog_ticks [] f_adler32_z_ticked adler32_z_buffer_ticked_spec.
Proof.
  start_function. unfold ticks, buffer_cost in *.
  assert (Hdiv : 0 <= Zlength bs / 5552 /\ 0 <= Zlength bs / 16)
    by (split; apply Z.div_pos; lia).
  spend_tick.
  pose proof (bytes_of_all_bytes bs) as Hbytes.
  pose proof (Zlength_bytes_of bs) as Hlen.
  pose proof (low16_range adler) as Hlow.
  pose proof (high16_range adler) as Hhigh.
  forward. forward.
  rewrite (Int.signed_repr 65535), (Int.unsigned_repr 16) by rep_lia.
  rewrite shr_high16, and_low16 by lia.
  assert_PROP (isptr buf) as Hptr by entailer!; fin.
  forward_if
    (PROP ()
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1))).
  { (* buf == Z_NULL cannot happen: the buffer is a real one *)
    exfalso. destruct buf; try contradiction.
    unfold nullval in *; simpl in *; discriminate. }
  { forward. entailer!; fin. }
  (* ---- one byte ---- *)
  forward_if
    (PROP (Zlength bs <> 1)
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1))).
  { norm_tests.
    load_byte. forward.
    rewrite byte_val, add64_repr.
    pose proof (Byte.unsigned_range_2 (Znth 0 bs)) as Hz.
    set (z0 := Byte.unsigned (Znth 0 bs)) in *.
    pose proof (Z.mod_pos_bound (low16 adler + z0) base base_pos) as Ha1.
    forward_if
      (PROP ()
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr ((low16 adler + z0) mod base)));
              temp _sum2 (Vlong (Int64.repr (high16 adler)));
              temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1))).
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
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr a1));
              temp _sum2 (Vlong (Int64.repr (sub_once (high16 adler + a1))));
              temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1))).
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
    Exists (sub_once (high16 adler + a1) * 65536 + a1) 1.
    rewrite pack_or by lia.
    entailer!; fin.
    apply spec_from_update. intros [Hh | Hn]; [|lia].
    rewrite (bytes_of_one bs) by assumption. fold z0.
    apply one_byte_update; [rep_lia | assumption]. }
  { norm_tests. forward. entailer!; fin. }
  Intros.
  (* ---- fewer than 16 bytes ---- *)
  forward_if
    (PROP (16 <= Zlength bs)
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf buf; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1))).
  { norm_tests.
    forward_loop
      (EX j : Z,
         PROP (0 <= j <= Zlength bs)
         LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                  (fst (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _sum2 (Vlong (Int64.repr
                  (snd (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _buf (offset_val j buf);
                temp _len (Vlong (Int64.repr (Zlength bs - j))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1 - j)))
      break:
      (PROP ()
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                (fst (acc (bytes_of bs) (low16 adler, high16 adler) 0
                          (Zlength bs)))));
              temp _sum2 (Vlong (Int64.repr
                (snd (acc (bytes_of bs) (low16 adler, high16 adler) 0
                          (Zlength bs))))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - Zlength bs))).
    - Exists 0. rewrite acc_start. entailer!; fin.
    - Intros j.
      spend_tick.
      forward. forward.
      forward_if
        (PROP (Zlength bs - j <> 0)
         LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                  (fst (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _sum2 (Vlong (Int64.repr
                  (snd (acc (bytes_of bs) (low16 adler, high16 adler) 0 j))));
                temp _buf (offset_val j buf);
                temp _len (Vlong (Int64.repr (Zlength bs - j - 1))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - j))).
      + norm_tests. forward. entailer!; fin.
      + norm_tests. assert (j = Zlength bs) by lia. subst j.
        forward. entailer!; fin.
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
         LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (X mod base)));
                temp _sum2 (Vlong (Int64.repr S)))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - Zlength bs))).
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
      Exists (S mod base * 65536 + X mod base) (Zlength bs + 2).
      rewrite pack_or by apply mod_base_bounds.
      pose proof (mod_base_bounds X). pose proof (mod_base_bounds S).
      entailer!; fin.
      apply spec_from_update. intros _.
      pose proof (short_result adler (bytes_of bs) ltac:(lia)) as Rr.
      cbv zeta in Rr. unfold modpair in Rr. cbn [fst snd] in Rr.
      rewrite Hlen in Rr. exact Rr. }
  { norm_tests. forward. entailer!; fin. }
  Intros.
  (* ---- the main loop, over blocks of 5552 bytes ---- *)
  forward_loop
    (EX b : Z, EX st : Z * Z,
       PROP (0 <= b; 5552 * b <= Zlength bs;
             block_ok adler (bytes_of bs) b st)
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (fst st)));
              temp _sum2 (Vlong (Int64.repr (snd st)));
              temp _buf (offset_val (5552 * b) buf);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1 - 348 * b)))
    break:
    (EX b : Z, EX st : Z * Z,
       PROP (0 <= b; 5552 * b <= Zlength bs; Zlength bs - 5552 * b < 5552;
             block_ok adler (bytes_of bs) b st)
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (fst st)));
              temp _sum2 (Vlong (Int64.repr (snd st)));
              temp _buf (offset_val (5552 * b) buf);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - 348 * b))).
  - Exists 0 (low16 adler, high16 adler).
    pose proof (block_ok_init adler (bytes_of bs)).
    entailer!; fin.
  - Intros b st.
    pose proof (div_facts (Zlength bs) b 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    spend_tick.
    forward_if
      (PROP (5552 <= Zlength bs - 5552 * b)
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (fst st)));
              temp _sum2 (Vlong (Int64.repr (snd st)));
              temp _buf (offset_val (5552 * b) buf);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - 348 * b))).
    + norm_tests. forward. entailer!; fin.
    + norm_tests. forward. Exists b st. entailer!; fin.
    + Intros. forward. forward.
      (* the inner loop: 347 iterations of 16 bytes each *)
      forward_loop
        (EX m : Z,
           PROP (0 <= m < 347)
           LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 5552)));
                  temp _n (Vint (Int.repr (347 - m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - 348 * b - m)))
        continue:
        (EX m : Z,
           PROP (0 <= m < 347)
           LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b)
                              (5552 * b + 16 * (m + 1))))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b)
                              (5552 * b + 16 * (m + 1))))));
                  temp _buf (offset_val (5552 * b + 16 * (m + 1)) buf);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 5552)));
                  temp _n (Vint (Int.repr (347 - m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 3 - 348 * b - m)))
        break:
        (PROP ()
         LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                  (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 5552)))));
                temp _sum2 (Vlong (Int64.repr
                  (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 5552)))));
                temp _buf (offset_val (5552 * (b + 1)) buf);
                temp _len (Vlong (Int64.repr (Zlength bs - 5552 * (b + 1)))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 1 - 348 * (b + 1)))).
      * Exists 0. rewrite inner_count.
        rewrite Z.mul_0_r, Z.add_0_r, acc_start. entailer!; fin.
      * Intros m.
        pose proof (div_facts (Zlength bs) b m ltac:(lia) ltac:(lia) ltac:(lia)).
        spend_tick.
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
      (EX u : Z,
       PROP (0 <= u <= Zlength bs / 5552 + Zlength bs / 16 + 19)
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                (fst (reduced_at (bytes_of bs) (low16 adler) (high16 adler)
                                 (Zlength bs)))));
              temp _sum2 (Vlong (Int64.repr
                (snd (reduced_at (bytes_of bs) (low16 adler) (high16 adler)
                                 (Zlength bs))))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - u))).
    + (* some bytes remain *)
      norm_tests.
      (* sixteen bytes at a time *)
      forward_loop
        (EX m : Z,
           PROP (0 <= m; 16 * m <= Zlength bs - 5552 * b)
           LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr
                               (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 2 - 348 * b - m)))
        break:
        (EX m : Z,
           PROP (0 <= m; 16 * m <= Zlength bs - 5552 * b;
                 Zlength bs - 5552 * b - 16 * m < 16)
           LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr
                               (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 3 - 348 * b - m))).
      * Exists 0. rewrite Z.mul_0_r, Z.add_0_r, acc_start. entailer!; fin.
      * Intros m.
        pose proof (div_facts (Zlength bs) b m ltac:(lia) ltac:(lia) ltac:(lia)).
        spend_tick.
        forward_if
          (PROP (16 <= Zlength bs - 5552 * b - 16 * m)
           LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (5552 * b + 16 * m)))));
                  temp _buf (offset_val (5552 * b + 16 * m) buf);
                  temp _len (Vlong (Int64.repr
                               (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 3 - 348 * b - m))).
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
        pose proof (div_facts (Zlength bs) b m ltac:(lia) ltac:(lia) ltac:(lia)).
        forward_loop
          (EX j : Z,
             PROP (0 <= j <= Zlength bs - 5552 * b - 16 * m)
             LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                      (fst (acc (bytes_of bs) st (5552 * b)
                                (5552 * b + 16 * m + j)))));
                    temp _sum2 (Vlong (Int64.repr
                      (snd (acc (bytes_of bs) st (5552 * b)
                                (5552 * b + 16 * m + j)))));
                    temp _buf (offset_val (5552 * b + 16 * m + j) buf);
                    temp _len (Vlong (Int64.repr
                                 (Zlength bs - 5552 * b - 16 * m - j))))
             SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 3 - 348 * b - m - j)))
          break:
          (PROP ()
           LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                    (fst (acc (bytes_of bs) st (5552 * b) (Zlength bs)))));
                  temp _sum2 (Vlong (Int64.repr
                    (snd (acc (bytes_of bs) st (5552 * b) (Zlength bs))))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 4 - 348 * b - m - (Zlength bs - 5552 * b - 16 * m)))).
        -- Exists 0. rewrite Z.add_0_r. entailer!; fin.
        -- Intros j. spend_tick. forward. forward.
           forward_if
             (PROP (Zlength bs - 5552 * b - 16 * m - j <> 0)
              LOCAL (gvars gv; temp _adler (Vlong (Int64.repr
                       (fst (acc (bytes_of bs) st (5552 * b)
                                 (5552 * b + 16 * m + j)))));
                     temp _sum2 (Vlong (Int64.repr
                       (snd (acc (bytes_of bs) st (5552 * b)
                                 (5552 * b + 16 * m + j)))));
                     temp _buf (offset_val (5552 * b + 16 * m + j) buf);
                     temp _len (Vlong (Int64.repr
                                  (Zlength bs - 5552 * b - 16 * m - j - 1))))
              SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf;
          tk gv (t - 4 - 348 * b - m - j))).
           ++ norm_tests. forward. entailer!; fin.
           ++ norm_tests. forward.
              replace (5552 * b + 16 * m + j) with (Zlength bs) by lia.
              entailer!; fin.
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
           pose proof (cost_tail (Zlength bs) b m ltac:(lia) ltac:(lia)
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
           Exists (4 + 348 * b + m + (Zlength bs - 5552 * b - 16 * m)).
           entailer!; fin.
    + (* no bytes remain: the input was a whole number of blocks *)
      norm_tests.
      pose proof (no_tail_result adler (bytes_of bs) b st Hok ltac:(lia)
                    ltac:(rewrite Zlength_bytes_of; lia)) as Hn.
      rewrite Hlen in Hn.
      pose proof (cost_whole_blocks (Zlength bs) b ltac:(lia) ltac:(lia)).
      forward. Exists (2 + 348 * b). rewrite <- Hn. entailer!; fin.
    + (* pack the two halves and return *)
      Intros u.
      destruct (reduced_at_bounds (bytes_of bs) (low16 adler) (high16 adler)
                  (Zlength bs)) as [Rf Rs].
      set (F := reduced_at (bytes_of bs) (low16 adler) (high16 adler)
                           (Zlength bs)) in *.
      forward.
      Exists (snd F * 65536 + fst F) u.
      rewrite pack_or by lia.
      entailer!; fin.
      apply spec_from_update. intros _.
      pose proof (update_from_reduced adler (bytes_of bs) ltac:(lia)) as U.
      cbv zeta in U. rewrite Hlen in U. exact U.
Qed.

(** ** The null buffer

    The function returns at once.  The only tick spent is the one on
    entry. *)

Lemma body_adler32_z_null_ticked :
  semax_body Vprog_ticks [] f_adler32_z_ticked adler32_z_null_ticked_spec.
Proof.
  start_function. unfold ticks in *.
  spend_tick.
  forward. forward.
  forward_if (PROP (False) LOCAL () SEP ()).
  - forward. Exists 1 1. entailer!; fin.
    apply Adler32Facts.adler32_initial_value. reflexivity.
  - (* the buffer is null, so the other branch cannot be taken *)
    exfalso. match goal with H : ?x <> ?x |- _ => apply H; reflexivity end.
Qed.

(** ** A buffer of length zero

    Two ticks: the one on entry, and one for the single test of the loop
    over the bytes, which fails at once.  The contract states the bound
    that the formula for a buffer gives at a length of zero, which is 19,
    so that it is the same bound as in the contract for every buffer. *)

Lemma body_adler32_z_empty_ticked :
  semax_body Vprog_ticks [] f_adler32_z_ticked adler32_z_empty_ticked_spec.
Proof.
  start_function. unfold ticks in *.
  (* the bound for a length of zero, by the formula *)
  change (buffer_cost 0) with 19 in *.
  pose proof (low16_range adler) as Hlow.
  pose proof (high16_range adler) as Hhigh.
  pose proof (Zlength_nonneg before) as Hbefore.
  pose proof (Zlength_nonneg after) as Hafter.
  assert (Hk : 0 <= Zlength before <= Zlength (before ++ after))
    by (rewrite Zlength_app; lia).
  assert (Hsh : sepalg.nonidentity sh) by assumption.
  assert (Hn : 0 < Zlength (before ++ after)) by assumption.
  set (bs := before ++ after) in *.
  set (k := Zlength before) in *.
  spend_tick.
  forward. forward.
  rewrite (Int.signed_repr 65535), (Int.unsigned_repr 16) by rep_lia.
  rewrite shr_high16, and_low16 by lia.
  assert_PROP (isptr arr) as Hptr by entailer!; fin.
  forward_if
    (PROP ()
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf (offset_val k arr); temp _len (Vlong (Int64.repr 0)))
     SEP (data_at sh (tarray tuchar (Zlength bs)) bs arr; tk gv (t - 1))).
  { (* the comparison with null is one C defines *)
    sep_apply (array_position_comparable sh bs arr k Hsh Hn Hk).
    eapply derives_trans;
      [ | apply comparable_with_null; destruct arr; try contradiction; exact I ].
    (* the counter's cell plays no part *)
    apply sepcon_weak_valid_pointer1. apply derives_refl. }
  { (* buf == Z_NULL cannot happen: the pointer is a real one *)
    exfalso. destruct arr; try contradiction.
    unfold nullval in *; simpl in *; discriminate. }
  { forward. entailer!; fin. }
  (* ---- the length is not one ---- *)
  forward_if
    (PROP ()
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf (offset_val k arr); temp _len (Vlong (Int64.repr 0)))
     SEP (data_at sh (tarray tuchar (Zlength bs)) bs arr; tk gv (t - 1))).
  { exfalso. norm_tests. lia. }
  { forward. entailer!; fin. }
  (* ---- fewer than 16 bytes: the branch taken ---- *)
  forward_if (PROP (False) LOCAL () SEP ()).
  2: { exfalso. norm_tests. lia. }
  forward_loop
    (PROP ()
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler)));
            temp _buf (offset_val k arr); temp _len (Vlong (Int64.repr 0)))
     SEP (data_at sh (tarray tuchar (Zlength bs)) bs arr; tk gv (t - 1)))
    break:
    (PROP ()
     LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler)));
            temp _sum2 (Vlong (Int64.repr (high16 adler))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) bs arr; tk gv (t - 2))).
  - entailer!; fin.
  - (* the loop test fails at once, so no byte is read *)
    spend_tick.
    forward. forward.
    forward_if (PROP (False) LOCAL () SEP ()).
    + exfalso. norm_tests. lia.
    + forward. entailer!; fin.
  - (* reduce, pack, and return *)
    unfold base in *.
    forward_if
      (PROP ()
       LOCAL (gvars gv; temp _adler (Vlong (Int64.repr (low16 adler mod base)));
              temp _sum2 (Vlong (Int64.repr (high16 adler))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) bs arr; tk gv (t - 2))).
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
    Exists (high16 adler mod base * 65536 + low16 adler mod base) 2.
    rewrite pack_or by apply mod_base_bounds.
    pose proof (mod_base_bounds (low16 adler)).
    pose proof (mod_base_bounds (high16 adler)).
    entailer!; fin.
    apply empty_result_spec.
Qed.
