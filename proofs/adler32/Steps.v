(** * Adler-32: one step of the C loop, in terms of the model

    Each unrolled step of the C code reads a byte, adds it to the first
    accumulator, and adds the first accumulator to the second.  These two
    lemmas say that the machine values after such a step are the model's
    accumulators one byte further on. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.proofs.adler32 Require Import Bridge Model.

Lemma acc_fst_step zs st lo k b :
  0 <= lo <= k -> k < Zlength zs -> Byte.unsigned b = Znth k zs ->
  Int64.add (Int64.repr (fst (acc zs st lo k)))
            (Int64.repr (Int.unsigned (Int.repr (Byte.unsigned b))))
  = Int64.repr (fst (acc zs st lo (k + 1))).
Proof.
  intros ? ? E. rewrite byte_val, add64_repr, acc_step by lia.
  unfold raw_step. cbn [fst]. rewrite E. reflexivity.
Qed.

Lemma acc_snd_step zs st lo k :
  0 <= lo <= k -> k < Zlength zs ->
  Int64.add (Int64.repr (snd (acc zs st lo k)))
            (Int64.repr (fst (acc zs st lo (k + 1))))
  = Int64.repr (snd (acc zs st lo (k + 1))).
Proof.
  intros. rewrite add64_repr, acc_step by lia.
  unfold raw_step. cbn [fst snd]. reflexivity.
Qed.
