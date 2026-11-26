(** * Adler-32 C proofs: what they rest on

    Every proof of a C function's contract in this directory, with the
    assumptions it depends on printed.  [tools/check_axioms.py] compiles
    this file and requires each printed axiom to be in
    [audit/allowed-axioms.txt].  It also requires every lemma here whose
    name starts with [body_] to be listed.

    The modules are required and not imported, so each axiom is printed
    under one fixed name. *)

From fvzlib.proofs.adler32 Require Verif VerifWrapper EmptyBuffer
  ContractProof ContractReview Combine WholeFile CombineGuarded.

(** The one statement for the whole file, which the claim in
    [claims/adler32.md] names. *)
Print Assumptions WholeFile.adler32_c_verified.

(** The contracts of [adler32_z] and [adler32], each covering every kind
    of buffer argument, and the lemmas that each narrower contract follows
    from them. *)
Print Assumptions ContractProof.body_adler32_z.
Print Assumptions ContractProof.body_adler32.
Print Assumptions ContractProof.adler32_z_contract_gives_null.
Print Assumptions ContractProof.adler32_z_contract_gives_buffer.
Print Assumptions ContractProof.adler32_z_contract_gives_empty.
Print Assumptions ContractProof.adler32_contract_gives_null.
Print Assumptions ContractProof.adler32_contract_gives_buffer.
Print Assumptions ContractProof.adler32_contract_gives_empty.

(** The checked statements behind the review of preconditions. *)
Print Assumptions ContractReview.any_ulong.
Print Assumptions ContractReview.any_uint.
Print Assumptions ContractReview.any_long.
Print Assumptions ContractReview.null_buffer_accepted.
Print Assumptions ContractReview.fresh_array_accepted.
Print Assumptions ContractReview.partly_filled_array_accepted.

(** The narrower contracts they are derived from: a null buffer, a
    non-empty buffer, and a non-null buffer of length zero. *)
Print Assumptions Verif.body_adler32_z_null.
Print Assumptions Verif.body_adler32_z_buffer.
Print Assumptions EmptyBuffer.body_adler32_z_empty.
Print Assumptions VerifWrapper.body_adler32_null.
Print Assumptions VerifWrapper.body_adler32_buffer.
Print Assumptions EmptyBuffer.body_adler32_empty.

(** The combine functions, and the guarded internal one. *)
Print Assumptions Combine.body_combine_internal.
Print Assumptions Combine.body_adler32_combine.
Print Assumptions Combine.body_adler32_combine64.
Print Assumptions CombineGuarded.body_combine_internal_guarded.
