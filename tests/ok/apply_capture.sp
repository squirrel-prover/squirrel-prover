

system null.

type E.
abstract ( ** ) : E -> E -> E.

abstract inv : E -> E.

axiom mult_inj (a,x,y : E) : a ** x = a ** y => x = y.

goal inv_inv (x : E) : x ** inv(inv(x)) = x ** x => inv(inv(x)) = x.
Proof.
  intro H.
  apply mult_inj x.
  assumption.  
Qed.
