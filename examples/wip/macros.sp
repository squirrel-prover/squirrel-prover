name n : message
term t : message = n

system null.

(* This does not parse: our support for user-defined macros is broken. *)

goal 
  t=n.
Proof.
Qed.
