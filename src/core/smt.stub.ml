let[@warning "-27"] is_valid
  ~macro_axioms ~timeout ~steps ~provers ~cmd_flag
  ~poly ~hint_tables env tbl system vars hyps hints concl
=
  Format.eprintf "SMT support unavailable, please recompile with Why3.@.";
  false
