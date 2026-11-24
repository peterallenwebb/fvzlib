(** Assumption audit for the Adler-32 specification layers.

    Every result listed here must be reported as "Closed under the global
    context", meaning it depends on no axiom at all.  The build checks
    this.  See tools/check_assumptions.py. *)

From fvzlib.format Require Import Adler32Facts.
From fvzlib.api Require Import Adler32Facts.

Print Assumptions Adler32Facts.update_1.
Print Assumptions Adler32Facts.s2_unreduced.
Print Assumptions Adler32Facts.second_sum_abc.
Print Assumptions Adler32Facts.adler32_range.
Print Assumptions Adler32Facts.update_adler32.
Print Assumptions Adler32Facts.update_app.
Print Assumptions Adler32Facts.s1_app.
Print Assumptions Adler32Facts.s2_app.
Print Assumptions Adler32Facts.prefixes_firstn.
Print Assumptions fvzlib.api.Adler32Facts.adler32_initial_value.
Print Assumptions fvzlib.api.Adler32Facts.adler32_reference_meets_spec.
Print Assumptions fvzlib.api.Adler32Facts.adler32_spec_deterministic.
Print Assumptions fvzlib.api.Adler32Facts.adler32_spec_range.
Print Assumptions fvzlib.api.Adler32Facts.usage_example.
Print Assumptions fvzlib.api.Adler32Facts.combine_reference_meets_spec.
Print Assumptions fvzlib.api.Adler32Facts.adler32_combine_spec_deterministic.
Print Assumptions fvzlib.api.Adler32Facts.adler32_combine_spec_negative.
