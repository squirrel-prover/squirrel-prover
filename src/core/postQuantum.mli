
(* [check_qatt_occs context ts] verifies the following syntactic
   conditions over ts:
   
   1) all the direct or indirect occurences of `qatt(u,v)` in ts can
    be unified with the pattern `qatt(qrnd tau, frame tau)`.
   
   2) there is a single occurence of a quantum level a top-level in the
   list [ts], that is, not under a function appliction.

   3) the only quantum values under functions are as the second
   argument of `qatt.


Those conditions notably imply that the list of terms can be produced by a
quantum simulator.
   
*)  
val check_quantum_simulable:
  ProofContext.t -> Term.term list -> bool
