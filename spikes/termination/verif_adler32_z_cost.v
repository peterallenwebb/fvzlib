(** * Spike: a VST cost contract for the instrumented adler32_z

    The function is the real [adler32_z] of patched zlib 1.4 with ticks
    added.  The contract proven here covers memory safety and cost only.  It
    says nothing about the value returned.  It is restricted to a non-null,
    non-empty buffer. *)

Require Import VST.floyd.proofauto.
Require Import adler32 Ticks adler32_ticked Buffer.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog_ticks : varspecs := [(_fvz_ticks, tulong)].

(** One tick on entry, one for each test of each loop condition. *)
Definition adler32_z_cost (len : Z) : Z := len / 5552 + len / 16 + 19.

Definition adler32_z_cost_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, sh : share, bs : list byte, base : val, gv : globals, t : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength bs <= Int64.max_unsigned;
          adler32_z_cost (Zlength bs) <= t <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); base; Vlong (Int64.repr (Zlength bs)))
    GLOBALS (gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
         ticks gv t)
  POST [ tulong ]
    EX r : int64, EX used : Z,
    PROP (0 <= used <= adler32_z_cost (Zlength bs))
    RETURN (Vlong r)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
         ticks gv (t - used)).

Definition Gprog_ticks : funspecs := [adler32_z_cost_spec].

(* Close goals about equal integer values and cells holding them. *)
Ltac fin1 :=
  first [ solve [lia]
        | solve [f_equal; lia]
        | solve [do 2 f_equal; lia]
        | solve [apply derives_refl'; do 3 f_equal; lia]
        | solve [cancel] ].
Ltac fin := repeat match goal with |- _ /\ _ => split end; try fin1.

(* Return, giving the returned value and the ticks used as witnesses. *)
Ltac return_using used :=
  forward;
  eapply exp_right; Exists used;
  entailer!; fin.

(* Turn a 64-bit equality test on two in-range integers into a fact. *)
Ltac int64_eq_true :=
  match goal with
  | H : Int64.eq (Int64.repr ?x) (Int64.repr ?y) = true |- _ =>
      apply Int64.same_if_eq in H; apply repr_inj_unsigned64 in H;
      [ | rep_lia | rep_lia ]
  end.
Ltac int64_eq_false :=
  match goal with
  | H : Int64.eq (Int64.repr ?x) (Int64.repr ?y) = false |- _ =>
      assert (x <> y)
        by (let Heq := fresh in intro Heq; rewrite Heq in H;
            rewrite Int64.eq_true in H; discriminate)
  end.

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
  end.

(* Name the current value of a temporary as the witness of an EX. *)
Ltac witness_of id :=
  match goal with |- context [temp id (Vlong ?v)] => Exists v end.

(** ** Arithmetic behind the cost bound

    5552 is 16 times 347, so a block of 5552 bytes takes 347 iterations of
    the inner loop. *)

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

Lemma inner_count : Int.divs (Int.repr 5552) (Int.repr 16) = Int.repr 347.
Proof. unfold Int.divs. rewrite !Int.signed_repr by rep_lia. reflexivity. Qed.

(* Split the buffer at position i, and put it back together. *)
Ltac split_at sh bs base i :=
  sep_apply (@split_buffer CompSpecs sh bs base i ltac:(lia));
  unfold suffix_at; Intros.
Ltac merge_at sh bs base i :=
  sep_apply (@merge_parts CompSpecs sh bs base i ltac:(lia) ltac:(assumption)).

(* Forget what the two running sums are.  This proof makes no claim about
   them, and their terms would otherwise grow with every byte read. *)
Ltac forget_sums :=
  match goal with |- context [temp _adler (Vlong ?a)] =>
    let x := fresh "a" in set (x := a); clearbody x end;
  match goal with |- context [temp _sum2 (Vlong ?s)] =>
    let x := fresh "s" in set (x := s); clearbody x end.

(* One unrolled step of the checksum: read a byte and update both sums. *)
Ltac do1 := load_byte; forward; forward; forget_sums.
Ltac do16 := do 16 do1.

Lemma body_adler32_z_cost :
  semax_body Vprog_ticks Gprog_ticks f_adler32_z_ticked adler32_z_cost_spec.
Proof.
  start_function. unfold ticks, adler32_z_cost in *.
  assert (Hdiv : 0 <= Zlength bs / 5552 /\ 0 <= Zlength bs / 16)
    by (split; apply Z.div_pos; lia).
  spend_tick.
  forward. forward.
  match goal with |- context [temp _adler (Vlong ?v)] => set (a0 := v) end.
  match goal with |- context [temp _sum2 (Vlong ?v)] => set (s0 := v) end.
  clearbody a0 s0.
  assert_PROP (isptr base) as Hptr by entailer!.
  forward_if
    (PROP ()
     LOCAL (temp _adler (Vlong a0); temp _sum2 (Vlong s0); gvars gv;
            temp _buf base; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
          data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { (* buf == Z_NULL cannot happen: the buffer is a real one *)
    exfalso. destruct base; try contradiction.
    unfold nullval in *; simpl in *; discriminate. }
  { forward. entailer!. }
  (* the one-byte path *)
  forward_if
    (PROP (Zlength bs <> 1)
     LOCAL (temp _adler (Vlong a0); temp _sum2 (Vlong s0); gvars gv;
            temp _buf base; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
          data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { int64_eq_true.
    load_byte. forward.
    forward_if
      (EX a1 : int64,
       PROP ()
       LOCAL (temp _adler (Vlong a1); temp _sum2 (Vlong s0); gvars gv;
              temp _buf base; temp _len (Vlong (Int64.repr (Zlength bs))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
            data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
    { forward. witness_of _adler. entailer!. }
    { forward. witness_of _adler. entailer!. }
    Intros a1. forward.
    forward_if
      (EX s1 : int64,
       PROP ()
       LOCAL (temp _adler (Vlong a1); temp _sum2 (Vlong s1); gvars gv;
              temp _buf base; temp _len (Vlong (Int64.repr (Zlength bs))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
            data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
    { forward. witness_of _sum2. entailer!. }
    { forward. witness_of _sum2. entailer!. }
    Intros s1.
    return_using 1. }
  { forward.
    assert (Zlength bs <> 1)
      by (intro E; match goal with
                   | H : Int64.repr _ <> Int64.repr _ |- _ =>
                       apply H; rewrite E; reflexivity
                   end).
    entailer!. }
  Intros.
  (* the short-buffer path *)
  forward_if
    (PROP (16 <= Zlength bs)
     LOCAL (temp _adler (Vlong a0); temp _sum2 (Vlong s0); gvars gv;
            temp _buf base; temp _len (Vlong (Int64.repr (Zlength bs))))
     SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
          data_at Ews tulong (Vlong (Int64.repr (t - 1))) (gv _fvz_ticks))).
  { norm_tests.
    forward_loop
      (EX j : Z, EX a : int64, EX s : int64,
         PROP (0 <= j <= Zlength bs)
         LOCAL (temp _adler (Vlong a); temp _sum2 (Vlong s); gvars gv;
                temp _buf (offset_val j base);
                temp _len (Vlong (Int64.repr (Zlength bs - j))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
              data_at Ews tulong (Vlong (Int64.repr (t - 1 - j)))
                      (gv _fvz_ticks)))
      break:
      (EX a : int64, EX s : int64,
         PROP ()
         LOCAL (temp _adler (Vlong a); temp _sum2 (Vlong s); gvars gv)
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
              data_at Ews tulong (Vlong (Int64.repr (t - 2 - Zlength bs)))
                      (gv _fvz_ticks))).
    - Exists 0 a0 s0. entailer!; fin.
    - Intros j a s.
      spend_tick.
      forward. forward.
      forward_if
        (PROP (Zlength bs - j <> 0)
         LOCAL (temp _adler (Vlong a); temp _sum2 (Vlong s); gvars gv;
                temp _buf (offset_val j base);
                temp _len (Vlong (Int64.repr (Zlength bs - j - 1))))
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
              data_at Ews tulong (Vlong (Int64.repr (t - 2 - j)))
                      (gv _fvz_ticks))).
      + forward. entailer!; fin.
      + norm_tests. forward. Exists a s. entailer!; fin.
      + Intros. forward. forward.
        split_at sh bs base j.
        assert (Hfa := @suffix_head_address CompSpecs bs base j ltac:(lia) ltac:(assumption)).
        load_byte. forward. forward.
        merge_at sh bs base j.
        Exists (j + 1). witness_of _adler. witness_of _sum2.
        entailer!; fin.
    - Intros a s.
      forward_if
        (EX a1 : int64,
         PROP ()
         LOCAL (temp _adler (Vlong a1); temp _sum2 (Vlong s); gvars gv)
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
              data_at Ews tulong (Vlong (Int64.repr (t - 2 - Zlength bs)))
                      (gv _fvz_ticks))).
      { forward. witness_of _adler. entailer!. }
      { forward. witness_of _adler. entailer!. }
      Intros a1. forward.
      return_using (Zlength bs + 2). }
  { norm_tests. forward. entailer!. }
  Intros.
  (* the main loop, over blocks of 5552 bytes *)
  forward_loop
    (EX b : Z, EX a : int64, EX s : int64,
       PROP (0 <= b; 5552 * b <= Zlength bs)
       LOCAL (temp _adler (Vlong a); temp _sum2 (Vlong s); gvars gv;
              temp _buf (offset_val (5552 * b) base);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
            data_at Ews tulong (Vlong (Int64.repr (t - 1 - 348 * b)))
                    (gv _fvz_ticks)))
    break:
    (EX b : Z, EX a : int64, EX s : int64,
       PROP (0 <= b; 5552 * b <= Zlength bs; Zlength bs - 5552 * b < 5552)
       LOCAL (temp _adler (Vlong a); temp _sum2 (Vlong s); gvars gv;
              temp _buf (offset_val (5552 * b) base);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
            data_at Ews tulong (Vlong (Int64.repr (t - 2 - 348 * b)))
                    (gv _fvz_ticks))).
  - Exists 0 a0 s0. entailer!; fin.
  - Intros b a s.
    pose proof (div_facts (Zlength bs) b 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    spend_tick.
    forward_if
      (PROP (5552 <= Zlength bs - 5552 * b)
       LOCAL (temp _adler (Vlong a); temp _sum2 (Vlong s); gvars gv;
              temp _buf (offset_val (5552 * b) base);
              temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b))))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
            data_at Ews tulong (Vlong (Int64.repr (t - 2 - 348 * b)))
                    (gv _fvz_ticks))).
    + norm_tests. forward. entailer!; fin.
    + norm_tests. forward. Exists b a s. entailer!; fin.
    + Intros. forward. forward.
      (* the inner loop: 347 iterations of 16 bytes each *)
      forward_loop
        (EX m : Z, EX a' : int64, EX s' : int64,
           PROP (0 <= m < 347)
           LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv;
                  temp _buf (offset_val (5552 * b + 16 * m) base);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 5552)));
                  temp _n (Vint (Int.repr (347 - m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                data_at Ews tulong (Vlong (Int64.repr (t - 2 - 348 * b - m)))
                        (gv _fvz_ticks)))
        continue:
        (EX m : Z, EX a' : int64, EX s' : int64,
           PROP (0 <= m < 347)
           LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv;
                  temp _buf (offset_val (5552 * b + 16 * (m + 1)) base);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 5552)));
                  temp _n (Vint (Int.repr (347 - m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                data_at Ews tulong (Vlong (Int64.repr (t - 3 - 348 * b - m)))
                        (gv _fvz_ticks)))
        break:
        (EX a' : int64, EX s' : int64,
           PROP ()
           LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv;
                  temp _buf (offset_val (5552 * (b + 1)) base);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * (b + 1)))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                data_at Ews tulong (Vlong (Int64.repr (t - 1 - 348 * (b + 1))))
                        (gv _fvz_ticks))).
      * Exists 0 a s. rewrite inner_count. entailer!; fin.
      * Intros m a' s'.
        pose proof (div_facts (Zlength bs) b m ltac:(lia) ltac:(lia) ltac:(lia)).
        spend_tick.
        split_at sh bs base (5552 * b + 16 * m).
        do16.
        forward.
        merge_at sh bs base (5552 * b + 16 * m).
        Exists m. witness_of _adler. witness_of _sum2.
        entailer!; fin.
      * (* the loop test, which counts n down *)
        Intros m a' s'.
        forward. forward.
        forward_if.
        -- norm_tests. forward. norm_tests.
           Exists (m + 1) a' s'. entailer!; fin.
        -- norm_tests. forward. norm_tests.
           Exists a' s'. entailer!; fin.
      * Intros a' s'.
        forward. forward.
        Exists (b + 1). witness_of _adler. witness_of _sum2.
        entailer!; fin.
  - (* after the main loop: fewer than 5552 bytes remain *)
    Intros b a s.
    forward_if
      (EX a' : int64, EX s' : int64, EX u : Z,
         PROP (0 <= u <= Zlength bs / 5552 + Zlength bs / 16 + 19)
         LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv)
         SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
              data_at Ews tulong (Vlong (Int64.repr (t - u))) (gv _fvz_ticks))).
    + (* some bytes remain *)
      norm_tests.
      (* sixteen bytes at a time *)
      forward_loop
        (EX m : Z, EX a' : int64, EX s' : int64,
           PROP (0 <= m; 16 * m <= Zlength bs - 5552 * b)
           LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv;
                  temp _buf (offset_val (5552 * b + 16 * m) base);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                data_at Ews tulong (Vlong (Int64.repr (t - 2 - 348 * b - m)))
                        (gv _fvz_ticks)))
        break:
        (EX m : Z, EX a' : int64, EX s' : int64,
           PROP (0 <= m; 16 * m <= Zlength bs - 5552 * b;
                 Zlength bs - 5552 * b - 16 * m < 16)
           LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv;
                  temp _buf (offset_val (5552 * b + 16 * m) base);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                data_at Ews tulong (Vlong (Int64.repr (t - 3 - 348 * b - m)))
                        (gv _fvz_ticks))).
      * Exists 0 a s. entailer!; fin.
      * Intros m a' s'.
        pose proof (div_facts (Zlength bs) b m ltac:(lia) ltac:(lia) ltac:(lia)).
        spend_tick.
        forward_if
          (PROP (16 <= Zlength bs - 5552 * b - 16 * m)
           LOCAL (temp _adler (Vlong a'); temp _sum2 (Vlong s'); gvars gv;
                  temp _buf (offset_val (5552 * b + 16 * m) base);
                  temp _len (Vlong (Int64.repr (Zlength bs - 5552 * b - 16 * m))))
           SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                data_at Ews tulong (Vlong (Int64.repr (t - 3 - 348 * b - m)))
                        (gv _fvz_ticks))).
        -- norm_tests. forward. entailer!; fin.
        -- norm_tests. forward. Exists m a' s'. entailer!; fin.
        -- Intros. forward.
           split_at sh bs base (5552 * b + 16 * m).
           do16.
           forward.
           merge_at sh bs base (5552 * b + 16 * m).
           Exists (m + 1). witness_of _adler. witness_of _sum2.
           entailer!; fin.
      * (* one byte at a time *)
        Intros m a' s'.
        pose proof (div_facts (Zlength bs) b m ltac:(lia) ltac:(lia) ltac:(lia)).
        forward_loop
          (EX j : Z, EX a'' : int64, EX s'' : int64,
             PROP (0 <= j <= Zlength bs - 5552 * b - 16 * m)
             LOCAL (temp _adler (Vlong a''); temp _sum2 (Vlong s''); gvars gv;
                    temp _buf (offset_val (5552 * b + 16 * m + j) base);
                    temp _len (Vlong (Int64.repr
                                 (Zlength bs - 5552 * b - 16 * m - j))))
             SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                  data_at Ews tulong
                          (Vlong (Int64.repr (t - 3 - 348 * b - m - j)))
                          (gv _fvz_ticks)))
          break:
          (EX a'' : int64, EX s'' : int64,
             PROP ()
             LOCAL (temp _adler (Vlong a''); temp _sum2 (Vlong s''); gvars gv)
             SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                  data_at Ews tulong
                          (Vlong (Int64.repr
                             (t - 4 - 348 * b - m
                              - (Zlength bs - 5552 * b - 16 * m))))
                          (gv _fvz_ticks))).
        -- Exists 0 a' s'. entailer!; fin.
        -- Intros j a'' s''.
           spend_tick.
           forward. forward.
           forward_if
             (PROP (Zlength bs - 5552 * b - 16 * m - j <> 0)
              LOCAL (temp _adler (Vlong a''); temp _sum2 (Vlong s''); gvars gv;
                     temp _buf (offset_val (5552 * b + 16 * m + j) base);
                     temp _len (Vlong (Int64.repr
                                  (Zlength bs - 5552 * b - 16 * m - j - 1))))
              SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base;
                   data_at Ews tulong
                           (Vlong (Int64.repr (t - 4 - 348 * b - m - j)))
                           (gv _fvz_ticks))).
           ++ norm_tests. forward. entailer!; fin.
           ++ norm_tests. forward. Exists a'' s''. entailer!; fin.
           ++ Intros. forward. forward.
              split_at sh bs base (5552 * b + 16 * m + j).
              assert (Hfa := @suffix_head_address CompSpecs bs base
                               (5552 * b + 16 * m + j)
                               ltac:(lia) ltac:(assumption)).
              load_byte. forward. forward.
              merge_at sh bs base (5552 * b + 16 * m + j).
              Exists (j + 1). witness_of _adler. witness_of _sum2.
              entailer!; fin.
        -- Intros a'' s''.
           forward. forward.
           pose proof (cost_tail (Zlength bs) b m ltac:(lia) ltac:(lia)
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
           witness_of _adler. witness_of _sum2.
           Exists (4 + 348 * b + m + (Zlength bs - 5552 * b - 16 * m)).
           entailer!; fin.
    + (* no bytes remain *)
      norm_tests.
      pose proof (cost_whole_blocks (Zlength bs) b ltac:(lia) ltac:(lia)).
      forward. Exists a s (2 + 348 * b). entailer!; fin.
    + Intros a' s' u.
      return_using u.
Qed.
