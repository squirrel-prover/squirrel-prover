axiom [any] foo (x,y : message): (x,y)#1 = y.

(* check that `foo` does apply, even modulo conversion (here, projection) *)
lemma [any] _ (a,b : message) : (a,b)#1 = b.
Proof. 
  rewrite /=. 
  checkfail rewrite foo exn Failure.
Abort.
