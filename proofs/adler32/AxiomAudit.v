(** * Adler-32 C proofs: what they rest on

    Every proof of a C function's contract in this directory, with the
    assumptions it depends on printed.  [tools/check_axioms.py] compiles
    this file and requires each printed axiom to be in
    [audit/allowed-axioms.txt].  It also requires every lemma here whose
    name starts with [body_] to be listed.

    The modules are required and not imported, so each axiom is printed
    under one fixed name. *)

From fvzlib.proofs.adler32 Require Verif VerifWrapper EmptyBuffer
  ContractProof ContractReview Combine VerifTicked CombineTicked
  CostContractProof WholeFile CombineGuarded StepBound.
From fvzlib.proofs.lib Require TickBound.

(** The one statement for the whole file, which the claim in
    [claims/adler32.md] names. *)
Print Assumptions WholeFile.adler32_c_verified.

(** The same for the functions with ticks and the contracts with a cost
    bound. *)
Print Assumptions WholeFile.adler32_c_verified_with_ticks.

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

(** The functions with ticks: the proofs about the code, and the single
    contract of [adler32_z] and of [adler32]. *)
Print Assumptions VerifTicked.body_adler32_z_null_ticked.
Print Assumptions VerifTicked.body_adler32_z_buffer_ticked.
Print Assumptions VerifTicked.body_adler32_z_empty_ticked.
Print Assumptions CombineTicked.body_combine_internal_ticked.
Print Assumptions CombineTicked.body_adler32_combine_ticked.
Print Assumptions CombineTicked.body_adler32_combine64_ticked.
Print Assumptions CostContractProof.body_adler32_z_ticked.
Print Assumptions CostContractProof.body_adler32_ticked.

(** Each written contract with ticks and its generated one follow from
    each other, and each generated one is the second form of its plain
    contract. *)
Print Assumptions CostContractProof.adler32_z_ticked_gives_generated.
Print Assumptions CostContractProof.adler32_z_generated_gives_ticked.
Print Assumptions CostContractProof.adler32_ticked_gives_generated.
Print Assumptions CostContractProof.adler32_generated_gives_ticked.
Print Assumptions CostContractProof.combine_internal_ticked_gives_generated.
Print Assumptions CostContractProof.combine_internal_generated_gives_ticked.
Print Assumptions CostContractProof.adler32_combine_ticked_gives_generated.
Print Assumptions CostContractProof.adler32_combine_generated_gives_ticked.
Print Assumptions CostContractProof.adler32_combine64_ticked_gives_generated.
Print Assumptions CostContractProof.adler32_combine64_generated_gives_ticked.
Print Assumptions CostContractProof.adler32_z_two_forms.
Print Assumptions CostContractProof.adler32_two_forms.
Print Assumptions CostContractProof.combine_internal_two_forms.
Print Assumptions CostContractProof.adler32_combine_two_forms.
Print Assumptions CostContractProof.adler32_combine64_two_forms.
Print Assumptions CostContractProof.adler32_z_ticked_contract_gives_null.
Print Assumptions CostContractProof.adler32_z_ticked_contract_gives_buffer.
Print Assumptions CostContractProof.adler32_z_ticked_contract_gives_empty.

(** That few ticks mean few steps: the general theorem, from
    [proofs/lib/TickBound.v], and what it gives for the five functions
    with ticks.  The two theorems are about executions.  They name the two
    parameters of CompCert's semantics, and rest on four of the six
    axioms, which CompCert's semantics brings into their statements.  The
    lemma between them is closed. *)
Print Assumptions TickBound.bounded_ticks_bound_steps_holds.
Print Assumptions TickBound.instrument_function_instrumented.
Print Assumptions StepBound.adler32_steps_bounded.
