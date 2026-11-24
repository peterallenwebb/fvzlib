(** * Bytes (Layer 1)

    Layer 1 states the formats as mathematics over sequences of integers.
    A byte is an integer from 0 to 255.  Definitions in this layer are total
    over all integer sequences, so they need no side conditions.  Statements
    that are only meant for genuine byte sequences say so with [all_bytes].

    This file may depend on the Rocq standard library only. *)

From Stdlib Require Import ZArith List.
Local Open Scope Z_scope.

(** A byte is an integer from 0 to 255. *)
Definition is_byte (z : Z) : Prop := 0 <= z < 256.

(** Every element of the sequence is a byte. *)
Definition all_bytes (l : list Z) : Prop := Forall is_byte l.
