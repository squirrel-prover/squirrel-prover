let[@warning "-27"] is_valid
  ~macro_axioms ~operator_axioms ~timeout ~steps ~provers ~cmd_flag
  ~poly ~exact ~hint_tables env vars hyps hints concl
=
  Format.eprintf "SMT support unavailable, please recompile with Why3.@.";
  false
