(** * Adler-32: proofs for [adler32]

    [adler32] passes its arguments to [adler32_z].  Each of its two
    contracts is proven from the corresponding contract of [adler32_z]. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Spec.

Lemma body_adler32_buffer :
  semax_body Vprog [adler32_z_buffer_spec; adler32_buffer_spec]
             f_adler32 adler32_buffer_spec.
Proof.
  start_function.
  forward_call (adler, sh, bs, buf).
  Intros r. forward. Exists r. entailer!.
Qed.

Lemma body_adler32_null :
  semax_body Vprog [adler32_z_null_spec; adler32_null_spec]
             f_adler32 adler32_null_spec.
Proof.
  start_function.
  forward_call (adler, len).
  Intros r. forward. Exists r. entailer!.
Qed.
