(** * Adler-32: C contracts (Layer 3)

    Contracts for [adler32_z] of patched zlib 1.4, stated against the
    Layer 2 specification, for two kinds of buffer argument: null, and
    non-empty.  [EmptyBuffer.v] adds a third, a non-null buffer of length
    zero.  These narrower contracts are what the C proofs establish.  The
    contract a caller should use is the single one in [Contract.v], which
    [ContractProof.v] derives from these.  None carries a cost clause.

    A contract here says three things about a call: it is memory safe, it
    leaves the buffer as it found it, and the value it returns satisfies the
    Layer 2 specification [adler32_spec]. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32 Adler32Facts.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** A non-null, non-empty buffer.  The checksum argument may be any 64-bit
    value.  The result is a 32-bit value that satisfies the Layer 2
    specification. *)
Definition adler32_z_buffer_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, sh : share, bs : list byte, buf : val
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength bs <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); buf; Vlong (Int64.repr (Zlength bs)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler (Some (bytes_of bs)) r; 0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf).

(** A null buffer, with any length.  The result is the initial value. *)
Definition adler32_z_null_spec : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, len : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); nullval; Vlong (Int64.repr len))
    SEP ()
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler None r)
    RETURN (Vlong (Int64.repr r))
    SEP ().

(** What the C proof establishes directly is an exact value, under a
    condition that every genuine running checksum meets.  This lemma turns
    that into the Layer 2 specification. *)
Lemma spec_from_update adler bs r :
  (high16 adler < base \/ Zlength bs <> 1 -> r = update adler (bytes_of bs)) ->
  adler32_spec adler (Some (bytes_of bs)) r.
Proof.
  intros H _ earlier [Hearlier ->]. split.
  - apply Forall_app. split; [assumption | apply bytes_of_all_bytes].
  - rewrite <- update_adler32. apply H. left.
    rewrite high16_adler32. apply s2_range.
Qed.

(** ** adler32

    The same two contracts for [adler32], whose length is a 32-bit
    [unsigned int]. *)

Definition adler32_buffer_spec : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, sh : share, bs : list byte, buf : val
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned; readable_share sh;
          0 < Zlength bs <= Int.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); buf; Vint (Int.repr (Zlength bs)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf)
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler (Some (bytes_of bs)) r; 0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) buf).

Definition adler32_null_spec : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, len : Z
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned; 0 <= len <= Int.max_unsigned)
    PARAMS (Vlong (Int64.repr adler); nullval; Vint (Int.repr len))
    SEP ()
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler None r)
    RETURN (Vlong (Int64.repr r))
    SEP ().
