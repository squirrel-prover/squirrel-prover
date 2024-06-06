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

(* ------------------------------------------------------------------- *)
global lemma _ (x,y : message) : [x = y => diff(x,x) = y].
Proof.
  simpl ~diffr.
  intro H.
  assumption H.
Qed. 

global lemma _ (x,y : message) : [x = y => diff(x,x) = y].
Proof.
  reduce ~diffr.
  intro H.
  assumption H.
Qed. 

global lemma _ (x,y : message) : [x = y => diff(x,x) = y].
Proof.
  auto ~diffr.
Qed. 
