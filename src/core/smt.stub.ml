type timestamp_style =
  | Abstract
  | Abstract_eq
  | Nat

let[@warning "-27"] is_valid
  ~timestamp_style ~pure ~slow ~prover tbl system vars hyps concl
=
  Format.eprintf "SMT support unavailable, please recompile with why3.@.";
  false