lemma _ @system:any : true <: Real.z.
Proof. true. Qed.

lemma _ @system:any : true <: Real.of_int 42.
Proof. 
  true. 
  have A : Real.z <= Real.of_int 42 by admit.
  assumption A.
Qed.
