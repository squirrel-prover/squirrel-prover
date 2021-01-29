system null.

goal forall (x:message,y:message,z:message),
  (x = y => y = z) => x = y => y = z.
Proof.
  nosimpl(intro x y z H Heq).
  nosimpl(apply H). 
  by assumption. 
  by assumption.
Qed.
