type timestamp_style =
  | Abstract
  | Abstract_eq
  | Nat

let[@warning "-27"] is_valid
  ~timestamp_style ~macro_axioms ~timeout ~steps ~provers
  tbl system vars hyps concl
=
  Format.eprintf "SMT support unavailable, please recompile with Why3.@.";
  false
