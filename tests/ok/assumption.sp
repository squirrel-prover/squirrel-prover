set autoIntro=false.
system null.

goal _ (x,y : message) : x = y => x = y.
Proof.
 intro H. 
 assumption.
Qed.

goal _ (x,y : message) : x = y => True.
Proof.
 intro H. 
 assumption.
Qed.

goal _ (x,y : message) : False => x = y.
Proof.
 intro H. 
 assumption.
Qed.
