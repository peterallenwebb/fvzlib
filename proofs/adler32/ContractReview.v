(** * Adler-32: checked statements behind the review of preconditions

    [audit/preconditions-adler32.toml] reviews every clause of the
    precondition of every contract in this directory.  Where a verdict in
    that review can be stated in Rocq, it is stated and proven here.

    - [any_ulong], [any_uint], [any_long]: a clause that bounds an argument
      by the range of its C type excludes no value of that type.
    - [null_buffer_accepted]: nothing is asked of a null buffer.
    - [fresh_array_accepted]: a call with a length of zero is covered for a
      pointer to an array that has never been written.
    - [partly_filled_array_accepted]: a call on the filled front of an
      array is covered whatever the rest of the array holds.

    The review also uses two results of the specification layers:
    [adler32_one_byte_changed] of Layer 1 and [checksum_form_iff] of
    Layer 2. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Spec Contract.

(** ** Clauses that only give an argument its C type

    A contract names each integer argument by a mathematical integer [z]
    and passes [Int64.repr z] or [Int.repr z].  The clause on [z] is the
    range of the C type.  Every value of the type is the image of some [z]
    in that range, so the clause rules out no call. *)

(** [unsigned long]: the checksum arguments, and the length of
    [adler32_z]. *)
Lemma any_ulong (v : int64) :
  exists z, 0 <= z <= Int64.max_unsigned /\ Int64.repr z = v.
Proof.
  exists (Int64.unsigned v). split; [rep_lia | apply Int64.repr_unsigned].
Qed.

(** [unsigned int]: the length of [adler32]. *)
Lemma any_uint (v : int) :
  exists z, 0 <= z <= Int.max_unsigned /\ Int.repr z = v.
Proof.
  exists (Int.unsigned v). split; [rep_lia | apply Int.repr_unsigned].
Qed.

(** [long]: the length of the combine functions. *)
Lemma any_long (v : int64) :
  exists z, Int64.min_signed <= z <= Int64.max_signed /\ Int64.repr z = v.
Proof.
  exists (Int64.signed v). split; [rep_lia | apply Int64.repr_signed].
Qed.

(** ** The buffer argument *)

(** A null buffer meets [buffer_ok] with any length, and lends no
    memory. *)
Lemma null_buffer_accepted (len : Z) (base : val) :
  buffer_ok Null len /\ buffer_ptr Null base = nullval /\
  buffer_rep Null base = emp.
Proof. repeat split. Qed.

(** An array of [n] cells that has never been written, with a length of
    zero.  The caller needs some part in the ownership of the array and
    nothing more.  This is the call a loop makes when its first read finds
    no data. *)
Lemma fresh_array_accepted sh (n : Z) (base : val) :
  sepalg.nonidentity sh -> 0 < n ->
  let b := Buffer sh [] [] (Zrepeat Vundef n) in
  buffer_ok b 0 /\ buffer_ptr b base = offset_val 0 base /\
  buffer_rep b base = data_at_ sh (tarray tuchar n) base.
Proof.
  intros Hsh Hn. cbn zeta.
  assert (Hlen : Zlength (buffer_array [] [] (Zrepeat Vundef n)) = n)
    by (unfold buffer_array; simpl; apply Zlength_Zrepeat; lia).
  repeat split.
  - assumption.
  - intros H. contradiction H. reflexivity.
  - lia.
  - unfold buffer_rep. rewrite Hlen. unfold buffer_array. simpl.
    rewrite data_at__tarray. reflexivity.
Qed.

(** The first bytes of an array are filled and the rest has never been
    written.  The filled part can be passed as it is. *)
Lemma partly_filled_array_accepted sh (bs : list byte) (m : Z) (base : val) :
  readable_share sh -> bs <> [] -> 0 <= m ->
  let b := Buffer sh [] bs (Zrepeat Vundef m) in
  buffer_ok b (Zlength bs) /\ buffer_ptr b base = offset_val 0 base /\
  buffer_rep b base
  = data_at sh (tarray tuchar (Zlength bs + m))
            (map Vubyte bs ++ Zrepeat Vundef m) base.
Proof.
  intros Hsh Hbs Hm. cbn zeta.
  assert (Hlen : Zlength (buffer_array [] bs (Zrepeat Vundef m))
                 = Zlength bs + m).
  { unfold buffer_array. simpl.
    rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia. reflexivity. }
  assert (0 < Zlength bs).
  { destruct bs; [contradiction |]. rewrite Zlength_cons.
    pose proof (Zlength_nonneg bs). lia. }
  repeat split.
  - apply readable_nonidentity. assumption.
  - intros _. assumption.
  - lia.
  - unfold buffer_rep. rewrite Hlen. reflexivity.
Qed.
