(** * The client program: what its results rest on

    Every result about executions, with the assumptions it depends on
    printed.  [tools/check_axioms.py] compiles this file.  A result here
    may depend on the six axioms in [audit/allowed-axioms.txt] and also on
    the five in [audit/execution-axioms.txt], which VST's soundness theorem
    and CompCert's semantics bring in.  That file says what each is.

    The modules are required and not imported, so each axiom is printed
    under one fixed name. *)

From fvzlib.proofs.lib Require Soundness GuardSound.
From fvzlib.proofs.adler32_client Require Client Guarded.

(** The two general theorems, which are about any program. *)
Print Assumptions Soundness.verified_program_never_goes_wrong.
Print Assumptions GuardSound.guards_removed.

(** The client: each function's contract, the whole program in VST's
    logic, and what follows for executions. *)
Print Assumptions Client.body_adler32_z.
Print Assumptions Client.body_adler32.
Print Assumptions Client.body_combine_internal.
Print Assumptions Client.body_adler32_combine.
Print Assumptions Client.body_adler32_combine64.
Print Assumptions Client.body_main.
Print Assumptions Client.client_verified.
Print Assumptions Client.client_never_goes_wrong.

(** The client with the guarded function, and what T0003 then gives for
    the client as written. *)
Print Assumptions Guarded.body_combine_internal_guarded_client.
Print Assumptions Guarded.guarded_verified.
Print Assumptions Guarded.guarded_never_goes_wrong.
Print Assumptions Guarded.client_tests_never_true.
Print Assumptions Guarded.remainder_operand_not_negative.
