system null.

axiom [default] toto : diff(true,false) = true.

axiom [default] tutu : false = true.

goal [default/right] _ : false = true.
Proof.
  by rewrite tutu. 
Qed.

abstract a : message.
abstract b : message.
abstract c : message.
abstract d : message.

axiom foo : diff(a,b) = c.

goal _ : 
  <a, diff(d, c)> = empty => 
  <a, diff(d, b)> = empty.
Proof.
  intro H. 
  rewrite foo.
  assumption.
Qed.

goal [default/right] _ : false = true.
Proof.
  rewrite toto.
  auto.
Qed.
