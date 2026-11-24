(** * Adler-32: test vectors for the format specification (Layer 1)

    Each line is checked by computation when this file is compiled.

    RFC 1950 gives no test vectors for Adler-32.  The expected values below
    were computed with a direct transcription of the RFC sample code and
    agree with zlib's own [adler32].  The comparison with zlib was made
    against the system library on the development machine.  It must be
    repeated against the pinned zlib release once that is in the build.

    The prose definition [adler32] takes time quadratic in the input, so it
    is tested on short inputs.  The sample-code definition [update] is tested
    on longer ones, including inputs long enough that a 32-bit accumulator
    would overflow if the reduction were delayed too far. *)

From Stdlib Require Import ZArith List String Ascii.
From fvzlib.format Require Import Adler32.
Import ListNotations.
Local Open Scope Z_scope.

(** The bytes of an ASCII string. *)
Definition bytes_of (s : string) : list Z :=
  map (fun c => Z.of_nat (nat_of_ascii c)) (list_ascii_of_string s).

(** ** The prose definition *)

Example prose_empty : adler32 [] = 1.
Proof. vm_compute. reflexivity. Qed.

Example prose_a : adler32 (bytes_of "a") = 0x00620062.
Proof. vm_compute. reflexivity. Qed.

Example prose_abc : adler32 (bytes_of "abc") = 0x024d0127.
Proof. vm_compute. reflexivity. Qed.

Example prose_message_digest :
  adler32 (bytes_of "message digest") = 0x29750586.
Proof. vm_compute. reflexivity. Qed.

Example prose_alphabet :
  adler32 (bytes_of "abcdefghijklmnopqrstuvwxyz") = 0x90860b20.
Proof. vm_compute. reflexivity. Qed.

Example prose_wikipedia : adler32 (bytes_of "Wikipedia") = 0x11e60398.
Proof. vm_compute. reflexivity. Qed.

(** RFC 1950, section 8.2: "If the bytes are a, b, c, the second sum is
    3a + 2b + c + 3".  Checked here on three bytes small enough that no
    reduction occurs. *)
Example prose_second_sum :
  s2 [10; 20; 30] = 3 * 10 + 2 * 20 + 30 + 3.
Proof. vm_compute. reflexivity. Qed.

(** ** The sample-code definition *)

Example code_alphabet :
  update 1 (bytes_of "abcdefghijklmnopqrstuvwxyz") = 0x90860b20.
Proof. vm_compute. reflexivity. Qed.

(** 5553 bytes of 255.  One more than the 5552 bytes for which RFC 1950,
    section 8.2, says the modulo can be delayed. *)
Example code_ff_5553 : update 1 (repeat 255 (Z.to_nat 5553)) = 0x8e299c8b.
Proof. vm_compute. reflexivity. Qed.

(** The 256 byte values in order, four times over. *)
Example code_all_bytes_x4 :
  let block := map Z.of_nat (seq 0 256) in
  update 1 (block ++ block ++ block ++ block) = 0xe4c9fe10.
Proof. vm_compute. reflexivity. Qed.

(** A thousand zero bytes.  The checksum still depends on the length. *)
Example code_zeros_1000 : update 1 (repeat 0 (Z.to_nat 1000)) = 0x03e80001.
Proof. vm_compute. reflexivity. Qed.

(** Computing in two pieces. *)
Example code_two_pieces :
  update (update 1 (bytes_of "message ")) (bytes_of "digest") = 0x29750586.
Proof. vm_compute. reflexivity. Qed.
