(** * Adler-32: the combine functions

    Contracts and proofs for [adler32_combine] and [adler32_combine64] of
    patched zlib 1.4, and for the internal function they both call.

    The contract says the value returned satisfies the Layer 2
    specification [adler32_combine_spec]: if the two arguments are the
    checksums of two byte sequences and the length is that of the second,
    the result is the checksum of their concatenation.  For arguments that
    are not checksums the manual promises nothing, and neither does this
    contract.  In particular it does not promise that the result fits in 32
    bits, which for such arguments it need not. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Spec.

(** [len2 % BASE], a signed 64-bit remainder, for a non-negative length. *)
Lemma mods_base x :
  0 <= x <= Int64.max_signed ->
  Int64.mods (Int64.repr x) (Int64.repr 65521) = Int64.repr (x mod base).
Proof.
  intros. unfold Int64.mods. rewrite !Int64.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

(** [(unsigned long)BASE << 1] *)
Lemma twice_base :
  Int64.shl (Int64.repr 65521) (Int64.repr 1) = Int64.repr 131042.
Proof.
  rewrite Int64.shl_mul_two_p. rewrite (Int64.unsigned_repr 1) by rep_lia.
  change (two_p 1) with 2. rewrite mul64_repr. reflexivity.
Qed.

(** The value the C code computes satisfies the specification. *)
Lemma combine_spec_from_values adler1 adler2 len2 :
  0 <= len2 ->
  adler32_combine_spec adler1 adler2 len2
    (Int64.unsigned
       (Int64.or
          (Int64.repr (sub_once (sub_once (low16 adler1 + low16 adler2 + 65520))))
          (Int64.shl
             (Int64.repr
                (sub_once (sub_twice
                   ((len2 mod base * low16 adler1) mod base
                    + high16 adler1 + high16 adler2 + 65521 - len2 mod base))))
             (Int64.repr 16)))).
Proof.
  intros Hlen seq1 seq2 [Hb1 E1] [Hb2 E2] Hl. subst adler1 adler2.
  rewrite !low16_adler32, !high16_adler32.
  pose proof (s1_range seq1). pose proof (s1_range seq2).
  pose proof (s2_range seq1). pose proof (s2_range seq2).
  rewrite combine_sum1 by assumption.
  rewrite combine_sum2 by assumption.
  rewrite pack_or by apply mod_base_bounds.
  pose proof (mod_base_bounds (s1 seq1 + s1 seq2 - 1)).
  pose proof (mod_base_bounds (s2 seq1 + s2 seq2 + len2 * (s1 seq1 - 1))).
  rewrite Int64.unsigned_repr by rep_lia.
  split.
  - apply Forall_app. split; assumption.
  - unfold adler32. rewrite s1_app, s2_app, <- Hl. reflexivity.
Qed.

(** ** Contracts *)

Definition combine_internal_spec : ident * funspec :=
 DECLARE _adler32_combine_
  WITH adler1 : Z, adler2 : Z, len2 : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned; 0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2))
    SEP ()
  POST [ tulong ]
    EX r : int64,
    PROP (adler32_combine_spec adler1 adler2 len2 (Int64.unsigned r))
    RETURN (Vlong r)
    SEP ().

(* Turn the machine-integer facts that a test leaves behind into facts
   about mathematical integers. *)
Ltac norm_tests :=
  repeat match goal with
  | H : context [Int.unsigned (Int.repr 65521)] |- _ =>
      rewrite (Int.unsigned_repr 65521) in H by rep_lia
  | H : context [Int.unsigned (Int.repr 1)] |- _ =>
      rewrite (Int.unsigned_repr 1) in H by rep_lia
  | H : context [Int64.shl (Int64.repr 65521) (Int64.repr 1)] |- _ =>
      rewrite twice_base in H
  | H : context [Int64.unsigned (Int64.repr ?x)] |- _ =>
      rewrite (Int64.unsigned_repr x) in H by rep_lia
  end.

(* Restate the value just assigned as a mathematical integer. *)
Ltac norm_value :=
  rewrite ?(Int.unsigned_repr 65521) by rep_lia;
  rewrite ?(Int.unsigned_repr 1) by rep_lia;
  rewrite ?twice_base; rewrite ?sub64_repr.

Ltac fin := try solve [do 2 f_equal; lia].

Lemma body_combine_internal :
  semax_body Vprog [combine_internal_spec] f_adler32_combine_
             combine_internal_spec.
Proof.
  start_function.
  pose proof (low16_range adler1) as L1. pose proof (low16_range adler2) as L2.
  pose proof (high16_range adler1) as H1'. pose proof (high16_range adler2) as H2'.
  forward_if
    (PROP (0 <= len2)
     LOCAL (temp _adler1 (Vlong (Int64.repr adler1));
            temp _adler2 (Vlong (Int64.repr adler2));
            temp _len2 (Vlong (Int64.repr len2)))
     SEP ()).
  { (* a negative length: the manual promises nothing *)
    rewrite !Int64.signed_repr in * by rep_lia.
    forward. eapply exp_right. entailer!.
    apply Adler32Facts.adler32_combine_spec_negative. lia. }
  { rewrite !Int64.signed_repr in * by rep_lia. forward. entailer!. }
  Intros.
  (* len2 %= BASE.  VST asks that this signed remainder is not the one
     overflowing case, the most negative value by minus one.  The divisor is
     65521, so it is not. *)
  forward.
  { entailer!.
    match goal with
    | H : _ /\ Int.repr 65521 = Int.mone |- _ =>
        destruct H as [_ H]; apply (f_equal Int.unsigned) in H;
        rewrite Int.unsigned_repr, Int.unsigned_mone in H by rep_lia; rep_lia
    end. }
  forward. forward. forward. forward. forward. forward.
  (* restate every machine value as a mathematical integer *)
  pose proof (Z.mod_pos_bound len2 base base_pos) as Hrem.
  assert (Hb : base = 65521) by reflexivity.
  rewrite !(Int.unsigned_repr 65521), !(Int.signed_repr 65535),
          !(Int.unsigned_repr 16), !(Int.signed_repr 1) by rep_lia.
  rewrite mods_base by rep_lia.
  rewrite (Int64.unsigned_repr (len2 mod base)) by rep_lia.
  rewrite (Int.unsigned_repr (len2 mod base)) by rep_lia.
  rewrite !and_low16, !shr_high16 by lia.
  rewrite mul64_repr.
  assert (Hprod : 0 <= len2 mod base * low16 adler1 <= Int64.max_unsigned)
    by (split; [nia | assert (len2 mod base * low16 adler1 <= 65521 * 65536) by nia; rep_lia]).
  rewrite modu_base by assumption.
  repeat first [rewrite add64_repr | rewrite sub64_repr].
  set (v1 := low16 adler1 + low16 adler2 + 65520).
  replace (low16 adler1 + (low16 adler2 + 65521 - 1)) with v1
    by (subst v1; lia).
  set (v2 := (len2 mod base * low16 adler1) mod base
             + high16 adler1 + high16 adler2 + 65521 - len2 mod base).
  replace ((len2 mod base * low16 adler1) mod base
           + (high16 adler1 + high16 adler2 + 65521 - len2 mod base))
    with v2 by (subst v2; lia).
  pose proof (mod_base_bounds (len2 mod base * low16 adler1)) as Hp.
  assert (Hv1 : 0 <= v1 <= 200000) by (subst v1; lia).
  assert (Hv2 : 0 <= v2 <= 300000) by (subst v2; lia).
  assert (E1 : v1 = low16 adler1 + low16 adler2 + 65520) by reflexivity.
  assert (E2 : v2 = (len2 mod base * low16 adler1) mod base
                    + high16 adler1 + high16 adler2 + 65521 - len2 mod base)
    by reflexivity.
  clearbody v1 v2.
  (* if (sum1 >= BASE) sum1 -= BASE; *)
  forward_if
    (PROP ()
     LOCAL (temp _sum1 (Vlong (Int64.repr (sub_once v1)));
            temp _sum2 (Vlong (Int64.repr v2)))
     SEP ()).
  { norm_tests. forward. norm_value.
    rewrite (sub_once_ge v1) by lia. entailer!; fin. }
  { norm_tests. forward. rewrite (sub_once_lt v1) by lia. entailer!. }
  pose proof (sub_once_bounds v1 ltac:(lia)) as Hs1.
  (* if (sum1 >= BASE) sum1 -= BASE; *)
  forward_if
    (PROP ()
     LOCAL (temp _sum1 (Vlong (Int64.repr (sub_once (sub_once v1))));
            temp _sum2 (Vlong (Int64.repr v2)))
     SEP ()).
  { norm_tests. forward. norm_value.
    rewrite (sub_once_ge (sub_once v1)) by lia. entailer!; fin. }
  { norm_tests. forward.
    rewrite (sub_once_lt (sub_once v1)) by lia. entailer!. }
  (* if (sum2 >= 2 * BASE) sum2 -= 2 * BASE; *)
  forward_if
    (PROP ()
     LOCAL (temp _sum1 (Vlong (Int64.repr (sub_once (sub_once v1))));
            temp _sum2 (Vlong (Int64.repr (sub_twice v2))))
     SEP ()).
  { norm_tests. forward. norm_value.
    rewrite (sub_twice_ge v2) by lia. entailer!; fin. }
  { norm_tests. forward. rewrite (sub_twice_lt v2) by lia. entailer!. }
  pose proof (sub_twice_bounds v2 ltac:(lia)) as Hs2.
  (* if (sum2 >= BASE) sum2 -= BASE; *)
  forward_if
    (PROP ()
     LOCAL (temp _sum1 (Vlong (Int64.repr (sub_once (sub_once v1))));
            temp _sum2 (Vlong (Int64.repr (sub_once (sub_twice v2)))))
     SEP ()).
  { norm_tests. forward. norm_value.
    rewrite (sub_once_ge (sub_twice v2)) by lia. entailer!; fin. }
  { norm_tests. forward.
    rewrite (sub_once_lt (sub_twice v2)) by lia. entailer!. }
  forward.
  eapply exp_right. entailer!.
  (* entailer! has already replaced v1 and v2 by what they stand for *)
  apply combine_spec_from_values. lia.
Qed.

(** ** The two exported functions

    Both pass their arguments straight to the internal function. *)

Definition adler32_combine_funspec : ident * funspec :=
 DECLARE _adler32_combine
  WITH adler1 : Z, adler2 : Z, len2 : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned; 0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2))
    SEP ()
  POST [ tulong ]
    EX r : int64,
    PROP (adler32_combine_spec adler1 adler2 len2 (Int64.unsigned r))
    RETURN (Vlong r)
    SEP ().

Definition adler32_combine64_funspec : ident * funspec :=
 DECLARE _adler32_combine64
  WITH adler1 : Z, adler2 : Z, len2 : Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= adler1 <= Int64.max_unsigned; 0 <= adler2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed)
    PARAMS (Vlong (Int64.repr adler1); Vlong (Int64.repr adler2);
            Vlong (Int64.repr len2))
    SEP ()
  POST [ tulong ]
    EX r : int64,
    PROP (adler32_combine_spec adler1 adler2 len2 (Int64.unsigned r))
    RETURN (Vlong r)
    SEP ().

Lemma body_adler32_combine :
  semax_body Vprog [combine_internal_spec; adler32_combine_funspec]
             f_adler32_combine adler32_combine_funspec.
Proof.
  start_function.
  forward_call (adler1, adler2, len2).
  Intros r. forward. Exists r. entailer!.
Qed.

Lemma body_adler32_combine64 :
  semax_body Vprog [combine_internal_spec; adler32_combine64_funspec]
             f_adler32_combine64 adler32_combine64_funspec.
Proof.
  start_function.
  forward_call (adler1, adler2, len2).
  Intros r. forward. Exists r. entailer!.
Qed.
