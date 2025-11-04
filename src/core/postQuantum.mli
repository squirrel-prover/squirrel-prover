
(* [check_direct_quantum_value_occurences context ts] verifies that
   there is a single direct occurence of a quantum value.

   <!> WIP:  Here, we just forbid two or more quantum values at top level. This is
     insufficient. We must check a stronger property, where the only
     allowed quantum value is state@tau_max.    
*)  
val check_direct_quantum_value_occurences :
  ProofContext.t -> Term.term list -> bool
