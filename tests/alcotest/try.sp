(* Verify that the failure to convert try-find terms to the congruence
   closure internal representation does not result in incorrect
   results. *)

abstract ok : message
abstract ko : message

system null.

goal _ : (try find i such that i=i in ok) = (try find i such that i=i in ko).
Proof.
  congruence.
