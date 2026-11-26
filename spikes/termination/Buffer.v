(** * Spike: reading a byte buffer through a moving pointer

    The Adler-32 code walks its buffer with a pointer.  VST reads through
    such a pointer once the buffer is split at the pointer's position: the
    bytes already passed stay at the base, and the rest sit at the pointer.
    These lemmas split the buffer and put it back together. *)

Require Import VST.floyd.proofauto.
From fvzlib.proofs.lib Require Import Ticks.

Section BufferLemmas.
Context {cs : compspecs}.

(** The buffer split at position [i]. *)
Definition suffix_at sh (bs : list byte) (base : val) (i : Z) : mpred :=
  (!! (field_compatible (tarray tuchar (Zlength bs)) [] base /\
       field_compatible (tarray tuchar (Zlength bs - i)) [] (offset_val i base)) &&
   (data_at sh (tarray tuchar i) (map Vubyte (sublist 0 i bs)) base *
    data_at sh (tarray tuchar (Zlength bs - i))
            (map Vubyte (sublist i (Zlength bs) bs)) (offset_val i base)))%logic.

Lemma buffer_split_eq sh bs base i :
  0 <= i <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] base ->
  data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base
  = (data_at sh (tarray tuchar i) (map Vubyte (sublist 0 i bs)) base *
     data_at sh (tarray tuchar (Zlength bs - i))
             (map Vubyte (sublist i (Zlength bs) bs)) (offset_val i base))%logic.
Proof.
  intros Hi Hfc. unfold tarray in *.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i (map Vubyte bs) base);
    [ | lia | list_solve ].
  rewrite !sublist_map.
  rewrite field_address0_offset by auto with field_compatible.
  simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

Lemma split_buffer sh bs base i :
  0 <= i <= Zlength bs ->
  data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base
  |-- suffix_at sh bs base i.
Proof.
  intros. unfold suffix_at.
  saturate_local.
  rewrite (buffer_split_eq sh bs base i) by auto.
  saturate_local.
  apply andp_right; [apply prop_right; split; [assumption |] | cancel].
  (* saturate_local states the fact with i replaced by a length equal to it *)
  match goal with
  | E : Zlength (map Vubyte (sublist 0 i bs)) = i,
    F : field_compatible _ [] (offset_val _ base) |- _ =>
      rewrite E in F; exact F
  end.
Qed.

Lemma merge_parts sh bs base i :
  0 <= i <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] base ->
  data_at sh (tarray tuchar i) (map Vubyte (sublist 0 i bs)) base *
  data_at sh (tarray tuchar (Zlength bs - i))
          (map Vubyte (sublist i (Zlength bs) bs)) (offset_val i base)
  |-- data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) base.
Proof. intros. rewrite (buffer_split_eq sh bs base i) by auto. cancel. Qed.

Lemma tc_Vubyte b : tc_val tuchar (Vubyte b).
Proof.
  unfold Vubyte. simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(** The address of the first byte of the rest of the buffer, in the form
    VST wants before it will read through a plain dereference. *)
Lemma suffix_head_address (bs : list byte) base j :
  0 <= j < Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs - j)) [] (offset_val j base) ->
  offset_val j base
  = field_address (tarray tuchar (Zlength bs - j)) (SUB 0) (offset_val j base).
Proof.
  intros. rewrite arr_field_address by (auto; lia). simpl.
  rewrite isptr_offset_val_zero; auto.
Qed.

End BufferLemmas.

(** Read one byte by index from the rest of the buffer, then expose the
    byte that was read. *)
Ltac load_byte :=
  forward;
  [ entailer!; apply tc_Vubyte
  | rewrite Znth_map by list_solve ].

(** Step through one tick when the counter is known to be positive.  The
    branch that jumps to the missing label is closed by contradiction. *)
Ltac spend_tick :=
  forward;
  forward_if True;
  [ exfalso;
    match goal with
    | H : Int64.repr _ = Int64.zero |- _ =>
        change Int64.zero with (Int64.repr 0) in H;
        apply repr_inj_unsigned64 in H; rep_lia
    end
  | forward; entailer!
  | forward ].

(** The tick resource: the counter holds [t]. *)
Definition ticks {cs : compspecs} (gv : globals) (t : Z) : mpred :=
  data_at Ews tulong (Vlong (Int64.repr t)) (gv _fvz_ticks).
