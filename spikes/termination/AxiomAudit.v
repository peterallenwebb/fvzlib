(** What the result of this spike rests on.  [tools/check_axioms.py]
    compiles this file and requires each printed axiom to be in
    [audit/allowed-axioms.txt]. *)

Require Twice.

Print Assumptions Twice.body_twice.
