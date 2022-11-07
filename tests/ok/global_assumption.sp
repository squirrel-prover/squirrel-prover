abstract a : message
abstract b : message

axiom [any] ax : a = b => False.

system null.

global goal _ (x:message) : [x = a && x = b] -> [false].
Proof.
  intro H.
  assert (x = a && x = b) as [H1 H2] by assumption.
  rewrite H1 in H2.
  by apply ax.
Qed.

(*------------------------------------------------------------------*)
global goal _ (x,y : message) : [false] -> equiv (diff(x,y)).
Proof. 
  intro H. 
  assumption H. 
Qed.

global goal _ (x,y : message) : [false] -> equiv (diff(x,y)).
Proof. 
  intro H. 
  assumption. 
Qed.
