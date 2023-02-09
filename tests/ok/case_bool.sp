system null.

goal _ (b:boolean) : b = true || b = false.
Proof.
  case b => _. 
  by left.  
  by right. 
Qed.
