

system null.

goal _ (x:message,y:message,z:message) :
  (x = y => y = z) => x = y => y = z.
Proof.
  nosimpl(intro H Heq).
  nosimpl(use H). 
  by assumption. 
  by assumption.
Qed.
