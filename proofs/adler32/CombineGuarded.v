(** * Adler-32: the open census item, closed

    The census for [adler32.c] has one open item: the signed remainder
    [len2 %= BASE] in the internal combine function.  Its result is
    implementation-defined in the 1990 C standard if [len2] is negative.

    This file applies the guard transformation to that function, which puts
    a test for a negative [len2] in front of the remainder, and proves the
    same contract for the guarded function.  Since VST can only prove the
    guard's jump unreachable, the proof shows [len2] is never negative
    there.

    The proof is the proof in [Combine.v] with one step added for the
    guard.  The steps are repeated here and not shared, which is a known
    weakness: we do not yet have a way to run one proof script against both
    the plain and the transformed form of a function. *)

Require Import VST.floyd.proofauto.
From compcert Require Import Clightdefs.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.api Require Adler32Facts.
From fvzlib.proofs.lib Require Import Census Guard.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Model Spec Combine.

(** The guarded function.  Computed, not written by hand.

    The tests to insert are decided first, by full computation.  They are
    then inserted by a computation that leaves the names in the function
    folded, so the result stays readable.

    The names to leave folded are the identifiers of this source file.
    CompCert's built-in functions are not listed.  Which of them exist
    depends on the target, and no function of [adler32.c] mentions one. *)
Definition f_adler32_combine__guarded : function :=
  ltac:(let plan := eval vm_compute in (guard_plan f_adler32_combine_) in
        match plan with
        | Some ?p =>
            let r := eval cbv -[_adler _adler1 _adler2 _adler32 _adler32_combine _adler32_combine64 _adler32_combine_ _adler32_z _buf _len _len2 _main _n _rem _sum1 _sum2 _t'1 _t'10 _t'11 _t'12 _t'13 _t'14 _t'15 _t'16 _t'17 _t'18 _t'19 _t'2 _t'20 _t'21 _t'22 _t'23 _t'24 _t'25 _t'26 _t'27 _t'28 _t'29 _t'3 _t'30 _t'31 _t'32 _t'33 _t'34 _t'35 _t'36 _t'37 _t'38 _t'39 _t'4 _t'40 _t'5 _t'6 _t'7 _t'8 _t'9
                                _fvz_undefined
                                tuchar tuint tint tulong tlong tptr tvoid
                                Int.repr Int64.repr cc_default]
                     in (apply_plan f_adler32_combine_ p) in
            exact r
        end).

(** It is what the transformation produces. *)
Example guarded_is_the_transformation :
  guard_function f_adler32_combine_ = Some f_adler32_combine__guarded.
Proof. vm_compute. reflexivity. Qed.

(** Removing the guards gives back the original. *)
Example erase_round_trip :
  erase_guards (fn_body f_adler32_combine__guarded) = fn_body f_adler32_combine_.
Proof. vm_compute. reflexivity. Qed.

(** One test was added, in front of the remainder. *)
Example one_guard :
  guard_plan f_adler32_combine_ <> None /\
  fn_body f_adler32_combine__guarded <> fn_body f_adler32_combine_.
Proof. split; vm_compute; discriminate. Qed.

(** The four functions with no open item are left unchanged. *)
Example nothing_to_guard :
  guard_function f_adler32_z = Some f_adler32_z /\
  guard_function f_adler32 = Some f_adler32 /\
  guard_function f_adler32_combine = Some f_adler32_combine /\
  guard_function f_adler32_combine64 = Some f_adler32_combine64.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma body_combine_internal_guarded :
  semax_body Vprog [combine_internal_spec] f_adler32_combine__guarded
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
  (* The guard: if (len2 < 0) goto fvz_undefined.  The length is known to
     be non-negative here, so the jump cannot be taken.  This is the proof
     that the remainder below never sees a negative operand. *)
  forward_if
    (PROP ()
     LOCAL (temp _adler1 (Vlong (Int64.repr adler1));
            temp _adler2 (Vlong (Int64.repr adler2));
            temp _len2 (Vlong (Int64.repr len2)))
     SEP ()).
  { exfalso.
    match goal with
    | Hlt : Int64.lt _ _ = true |- _ =>
        unfold Int64.lt in Hlt;
        destruct (zlt _ _) as [Hz|]; [|discriminate Hlt]
    end.
    rewrite (Int64.signed_repr len2) in Hz by rep_lia.
    (* the zero in the test is a computed constant: evaluate it *)
    match type of Hz with
    | context [Int.signed ?c] =>
        let v := eval vm_compute in (Int.signed c) in
        change (Int.signed c) with v in Hz
    end.
    rewrite Int64.signed_repr in Hz by rep_lia. lia. }
  { forward. entailer!. }
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
