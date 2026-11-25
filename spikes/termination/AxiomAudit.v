(** What the results of this spike rest on.  [tools/check_axioms.py]
    compiles this file and requires each printed axiom to be in
    [audit/allowed-axioms.txt]. *)

Require verif_adler32_z_cost verif_adler32_cost verif_combine_cost.

Print Assumptions verif_adler32_z_cost.body_adler32_z_cost.
Print Assumptions verif_adler32_cost.body_adler32_cost.
Print Assumptions verif_adler32_cost.body_twice.
Print Assumptions verif_combine_cost.body_combine_internal_cost.
Print Assumptions verif_combine_cost.body_adler32_combine_cost.
Print Assumptions verif_combine_cost.body_adler32_combine64_cost.
