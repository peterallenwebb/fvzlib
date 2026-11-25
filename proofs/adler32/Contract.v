(** * Adler-32: the contracts of [adler32_z] and [adler32] (Layer 3)

    One contract for each function, covering every call the manual allows.
    A downstream proof imports these.  [Spec.v] and [EmptyBuffer.v] hold
    three narrower contracts per function, one for each kind of buffer
    argument.  [ContractProof.v] derives the contracts here from those
    three, and shows that each of the three follows from the one here.

    This file holds definitions only.

    A contract says three things about a call: it is memory safe, it leaves
    the caller's memory as it found it, and the value it returns is a
    32-bit value that satisfies the Layer 2 specification [adler32_spec].
    The checksum argument may be any 64-bit value, and the length any value
    of its C type.  These contracts carry no cost clause yet. *)

Require Import VST.floyd.proofauto.
From fvzlib.format Require Import Bytes Adler32.
From fvzlib.api Require Import Adler32.
From fvzlib.proofs.adler32 Require Import adler32_clight Bridge Spec.

(** ** The buffer argument

    What the caller passes as [buf].  It is either the null pointer, or a
    run of bytes [bs] inside an array that the caller owns and may read.
    [before] holds the bytes of the array in front of the run and [after]
    the bytes behind it.  Either may be empty.

    The run itself may be empty, which is the call with a length of zero.
    The array as a whole may not be.  The code compares [buf] with null,
    and C gives that comparison a meaning only for a null pointer and for a
    pointer into, or one past the end of, an object.  A position in a
    non-empty array is such a pointer. *)
Inductive buffer_arg :=
| Null
| Buffer (sh : share) (before bs after : list byte).

(** The buffer as the Layer 2 specification sees it: no buffer, or the
    bytes of the run. *)
Definition buffer_model (b : buffer_arg) : option (list Z) :=
  match b with Null => None | Buffer _ _ bs _ => Some (bytes_of bs) end.

(** The pointer passed.  [base] is the start of the caller's array.  It
    plays no part for a null buffer. *)
Definition buffer_ptr (b : buffer_arg) (base : val) : val :=
  match b with
  | Null => nullval
  | Buffer _ before _ _ => offset_val (Zlength before) base
  end.

(** What the caller must ensure: the array is readable and not empty, and
    [len] is the length of the run.  Nothing is asked of a null buffer,
    whatever [len] is. *)
Definition buffer_ok (b : buffer_arg) (len : Z) : Prop :=
  match b with
  | Null => True
  | Buffer sh before bs after =>
      readable_share sh /\ Zlength bs = len /\
      0 < Zlength (before ++ bs ++ after)
  end.

(** The memory the caller lends for the call: the whole array, or nothing
    for a null buffer.  It appears unchanged in the postcondition. *)
Definition buffer_rep (b : buffer_arg) (base : val) : mpred :=
  match b with
  | Null => emp
  | Buffer sh before bs after =>
      data_at sh (tarray tuchar (Zlength (before ++ bs ++ after)))
              (map Vubyte (before ++ bs ++ after)) base
  end.

(** ** adler32_z *)

Definition adler32_z_contract : ident * funspec :=
 DECLARE _adler32_z
  WITH adler : Z, b : buffer_arg, base : val, len : Z
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned;
          0 <= len <= Int64.max_unsigned;
          buffer_ok b len)
    PARAMS (Vlong (Int64.repr adler); buffer_ptr b base;
            Vlong (Int64.repr len))
    SEP (buffer_rep b base)
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler (buffer_model b) r; 0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
    SEP (buffer_rep b base).

(** ** adler32

    The same contract.  Only the C type of the length differs: it is a
    32-bit [unsigned int]. *)

Definition adler32_contract : ident * funspec :=
 DECLARE _adler32
  WITH adler : Z, b : buffer_arg, base : val, len : Z
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned;
          0 <= len <= Int.max_unsigned;
          buffer_ok b len)
    PARAMS (Vlong (Int64.repr adler); buffer_ptr b base;
            Vint (Int.repr len))
    SEP (buffer_rep b base)
  POST [ tulong ]
    EX r : Z,
    PROP (adler32_spec adler (buffer_model b) r; 0 <= r < 4294967296)
    RETURN (Vlong (Int64.repr r))
    SEP (buffer_rep b base).
