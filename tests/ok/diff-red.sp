system null.

lemma _ (x,y : message) : x = y => diff(x,x) = y.
Proof.
  intro H. 
  simpl ~diffr.
  assumption H.
Qed. 

lemma _ (x,y : message) : x = y => diff(x,x) = y.
Proof.
  intro H.
  reduce ~diffr.
  assumption H.
Qed. 

lemma _ (x,y : message) : x = y => diff(x,x) = y.
Proof.
  intro H. 
  auto ~diffr.
Qed. 
