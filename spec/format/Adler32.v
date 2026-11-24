(** * Adler-32: format specification (Layer 1)

    Source: RFC 1950, "ZLIB Compressed Data Format Specification version 3.3",
    section 2.2 (the ADLER32 field) and section 9 (sample code).

    This file is trusted reading.  It contains definitions only.  Evidence
    that the definitions are right is in [Adler32Facts.v] and
    [Adler32Tests.v], and is not needed to understand what is claimed.

    There are two definitions of the checksum here, on purpose.

    - [adler32] transcribes the prose of section 2.2.
    - [update] transcribes the sample code of section 9.

    [Adler32Facts.v] proves that they agree.  Two independent readings of the
    RFC that are proven equal are less likely to share a mistake than one.

    This file may depend on the Rocq standard library only. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The prose definition (RFC 1950, section 2.2)

    "Adler-32 is composed of two sums accumulated per byte: s1 is the sum of
    all bytes, s2 is the sum of all s1 values. Both sums are done modulo
    65521. s1 is initialized to 1, s2 to zero. The Adler-32 checksum is
    stored as s2*65536 + s1 in most-significant-byte first (network)
    order." *)

(** "Both sums are done modulo 65521." *)
Definition base : Z := 65521.

(** The sum of a sequence of integers. *)
Definition sum (l : list Z) : Z := fold_right Z.add 0 l.

(** The non-empty prefixes of a sequence, shortest first.  The sums are
    "accumulated per byte", so there is one s1 value for each byte consumed,
    that is, one for each non-empty prefix of the input. *)
Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: rest => [x] :: map (cons x) (prefixes rest)
  end.

(** "s1 is the sum of all bytes ... s1 is initialized to 1" *)
Definition s1 (bytes : list Z) : Z := (1 + sum bytes) mod base.

(** "s2 is the sum of all s1 values ... s2 [is initialized] to zero" *)
Definition s2 (bytes : list Z) : Z := (0 + sum (map s1 (prefixes bytes))) mod base.

(** "The Adler-32 checksum is ... s2*65536 + s1".  How the value is laid out
    in a zlib stream is part of the zlib stream format, not of this file. *)
Definition adler32 (bytes : list Z) : Z := s2 bytes * 65536 + s1 bytes.

(** ** The sample code (RFC 1950, section 9)

<<
      unsigned long update_adler32(unsigned long adler,
         unsigned char *buf, int len)
      {
        unsigned long s1 = adler & 0xffff;
        unsigned long s2 = (adler >> 16) & 0xffff;
        int n;

        for (n = 0; n < len; n++) {
          s1 = (s1 + buf[n]) % BASE;
          s2 = (s2 + s1)     % BASE;
        }
        return (s2 << 16) + s1;
      }
>>
*)

(** One iteration of the loop.  The state is the pair (s1, s2). *)
Definition step (state : Z * Z) (byte : Z) : Z * Z :=
  let s1' := (fst state + byte) mod base in
  let s2' := (snd state + s1') mod base in
  (s1', s2').

(** [adler & 0xffff] *)
Definition low16 (adler : Z) : Z := adler mod 65536.

(** [(adler >> 16) & 0xffff] *)
Definition high16 (adler : Z) : Z := (adler / 65536) mod 65536.

(** [update_adler32]: continue a running checksum over more bytes. *)
Definition update (adler : Z) (bytes : list Z) : Z :=
  let final := fold_left step bytes (low16 adler, high16 adler) in
  snd final * 65536 + fst final.
