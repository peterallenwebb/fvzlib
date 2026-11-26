(** What the results of this spike rest on.  [tools/check_axioms.py]
    compiles this file and requires each printed axiom to be in
    [audit/allowed-axioms.txt]. *)

Require Transfer verif_toy_nogoto verif_toy_ticked TickBound.

Print Assumptions Transfer.toy_goto_target.
Print Assumptions verif_toy_nogoto.body_count_down_nogoto.
Print Assumptions verif_toy_ticked.body_count_down_ticked.
Print Assumptions TickBound.bounded_ticks_bound_steps_holds.
Print Assumptions TickBound.instrument_function_instrumented.
