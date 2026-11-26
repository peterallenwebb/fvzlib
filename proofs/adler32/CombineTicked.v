(** * Adler-32: the combine functions with ticks (Layer 4)

    VST proofs about the three combine functions with a counter added.
    Each contract says what the plain contract in [Combine.v] says, and
    also how many ticks the call spends: 1 for the internal function, and
    2 for each exported function, which spends one and calls the internal
    one.  None has a loop.

    The proof for the internal function repeats the steps of the plain
    proof, with one more step for its tick. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.lib Require Import Ticks TickLogic.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Spec
  Contract Ticked CostContract.
(* Last, so that its tactics are the ones in force. *)
From fvzlib.proofs.adler32 Require Import Combine.

(** The cell that holds the counter, as the proofs below see it. *)
Local Abbreviation tk gv x :=
  (data_at Ews tulong (Vlong (Int64.repr x)) (gv _fvz_ticks)).

(** ** The internal function *)

Lemma body_combine_internal_ticked :
  semax_body Vprog_ticks [] f_adler32_combine__ticked
             combine_internal_ticked_spec.
Proof.
  start_function. unfold ticks, combine_internal_cost in *.
  spend_tick.
  pose proof (low16_range adler1) as L1. pose proof (low16_range adler2) as L2.
  pose proof (high16_range adler1) as H1'. pose proof (high16_range adler2) as H2'.
  forward_if
    (PROP (0 <= len2)
     LOCAL (gvars gv; temp _adler1 (Vlong (Int64.repr adler1));
            temp _adler2 (Vlong (Int64.repr adler2));
            temp _len2 (Vlong (Int64.repr len2)))
     SEP (tk gv (t - 1))).
  { (* a negative length: the manual promises nothing *)
    rewrite !Int64.signed_repr in * by rep_lia.
    forward. eapply exp_right. Exists 1. entailer!.
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
     LOCAL (gvars gv; temp _sum1 (Vlong (Int64.repr (sub_once v1)));
            temp _sum2 (Vlong (Int64.repr v2)))
     SEP (tk gv (t - 1))).
  { norm_tests. forward. norm_value.
    rewrite (sub_once_ge v1) by lia. entailer!; fin. }
  { norm_tests. forward. rewrite (sub_once_lt v1) by lia. entailer!. }
  pose proof (sub_once_bounds v1 ltac:(lia)) as Hs1.
  (* if (sum1 >= BASE) sum1 -= BASE; *)
  forward_if
    (PROP ()
     LOCAL (gvars gv; temp _sum1 (Vlong (Int64.repr (sub_once (sub_once v1))));
            temp _sum2 (Vlong (Int64.repr v2)))
     SEP (tk gv (t - 1))).
  { norm_tests. forward. norm_value.
    rewrite (sub_once_ge (sub_once v1)) by lia. entailer!; fin. }
  { norm_tests. forward.
    rewrite (sub_once_lt (sub_once v1)) by lia. entailer!. }
  (* if (sum2 >= 2 * BASE) sum2 -= 2 * BASE; *)
  forward_if
    (PROP ()
     LOCAL (gvars gv; temp _sum1 (Vlong (Int64.repr (sub_once (sub_once v1))));
            temp _sum2 (Vlong (Int64.repr (sub_twice v2))))
     SEP (tk gv (t - 1))).
  { norm_tests. forward. norm_value.
    rewrite (sub_twice_ge v2) by lia. entailer!; fin. }
  { norm_tests. forward. rewrite (sub_twice_lt v2) by lia. entailer!. }
  pose proof (sub_twice_bounds v2 ltac:(lia)) as Hs2.
  (* if (sum2 >= BASE) sum2 -= BASE; *)
  forward_if
    (PROP ()
     LOCAL (gvars gv; temp _sum1 (Vlong (Int64.repr (sub_once (sub_once v1))));
            temp _sum2 (Vlong (Int64.repr (sub_once (sub_twice v2)))))
     SEP (tk gv (t - 1))).
  { norm_tests. forward. norm_value.
    rewrite (sub_once_ge (sub_twice v2)) by lia. entailer!; fin. }
  { norm_tests. forward.
    rewrite (sub_once_lt (sub_twice v2)) by lia. entailer!. }
  forward.
  eapply exp_right. Exists 1. entailer!.
  (* entailer! has already replaced v1 and v2 by what they stand for *)
  apply combine_spec_from_values. lia.
Qed.

(** ** The two exported functions

    Each spends a tick, calls the internal function with what is left of
    its budget, and returns what that returned. *)
Ltac call_internal adler1 adler2 len2 gv t :=
  unfold adler32_combine_cost, combine_internal_cost in *;
  unfold ticks;
  spend_tick;
  forward_call (adler1, adler2, len2, gv, t - 1);
  [ unfold ticks; rewrite sub64_repr; cancel | ];
  let vret := fresh "vret" in
  let r := fresh "r" in
  let used := fresh "used" in
  Intros vret; destruct vret as [r used]; cbn [fst snd] in *;
  unfold combine_internal_cost in *;
  forward;
  Exists r (used + 1); unfold ticks; entailer!;
  apply derives_refl'; do 3 f_equal; lia.

Lemma body_adler32_combine_ticked :
  semax_body Vprog_ticks
             [combine_internal_ticked_spec; adler32_combine_ticked_funspec]
             f_adler32_combine_ticked adler32_combine_ticked_funspec.
Proof. start_function. call_internal adler1 adler2 len2 gv t. Qed.

Lemma body_adler32_combine64_ticked :
  semax_body Vprog_ticks
             [combine_internal_ticked_spec; adler32_combine64_ticked_funspec]
             f_adler32_combine64_ticked adler32_combine64_ticked_funspec.
Proof. start_function. call_internal adler1 adler2 len2 gv t. Qed.
