(** * Adler-32: API behavior (Layer 2)

    Source: the zlib manual, [zlib.h], release 1.4, the entries for
    [adler32], [adler32_z], and [adler32_combine].

    This file is trusted reading.  It contains definitions only.  It says
    what the manual promises about results, in terms of the format
    specification of Layer 1.  It says nothing about C, memory, or cost.
    Those belong to Layer 3.

    Each specification is a relation between arguments and a result.  Where
    the manual makes no promise, the relation allows any result.

    This file may depend on the Rocq standard library and Layer 1 only. *)

From Stdlib Require Import ZArith List.
From fvzlib.format Require Import Bytes Adler32.
Import ListNotations.
Local Open Scope Z_scope.

(** [adler] is the Adler-32 checksum of the byte sequence [data].  The manual
    calls such a value a "running Adler-32 checksum" when more data may
    follow. *)
Definition running_checksum (adler : Z) (data : list Z) : Prop :=
  all_bytes data /\ adler = adler32 data.

(** ** adler32 and adler32_z

    "Update a running Adler-32 checksum with the bytes buf[0..len-1] and
    return the updated checksum. An Adler-32 value is in the range of a
    32-bit unsigned integer. If buf is Z_NULL, this function returns the
    required initial value for the checksum."

    For [adler32_z]: "Same as adler32(), but with a size_t length."

    The argument [buf] is [None] for [Z_NULL], and otherwise the bytes
    buf[0..len-1].

    - With [Z_NULL], the result is the checksum of no data at all, which is
      the value from which a running checksum must start.
    - Otherwise, if [adler] is the running checksum of some earlier data,
      the result is the running checksum of that data followed by the new
      bytes.  If [adler] is not a running checksum of anything, the manual
      promises nothing. *)
Definition adler32_spec (adler : Z) (buf : option (list Z)) (result : Z) : Prop :=
  match buf with
  | None => running_checksum result []
  | Some bytes =>
      all_bytes bytes ->
      forall earlier,
        running_checksum adler earlier ->
        running_checksum result (earlier ++ bytes)
  end.

(** ** adler32_combine

    "Combine two Adler-32 checksums into one. For two sequences of bytes,
    seq1 and seq2 with lengths len1 and len2, Adler-32 checksums were
    calculated for each, adler1 and adler2. adler32_combine() returns the
    Adler-32 checksum of seq1 and seq2 concatenated, requiring only adler1,
    adler2, and len2. Note that the z_off_t type (like off_t) is a signed
    integer. If len2 is negative, the result has no meaning or utility."

    No sequence has a negative length, so for negative [len2] this relation
    allows any result, as the manual says. *)
Definition adler32_combine_spec (adler1 adler2 len2 result : Z) : Prop :=
  forall seq1 seq2,
    running_checksum adler1 seq1 ->
    running_checksum adler2 seq2 ->
    len2 = Z.of_nat (length seq2) ->
    running_checksum result (seq1 ++ seq2).
