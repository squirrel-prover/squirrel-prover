type a.
type b.

abstract a : a.
abstract b : b.
abstract p: a -> b -> bool.

axiom [any] lem : forall (x:a, y:b), p x y.
axiom [any] lem1 (x:a, y:b): p x y.

print lem.

(* check that variables order is not inversed when instanciating a lemma *)
lemma [any] _ : false.
Proof. 
have H := lem.
have H1:= lem1.
have A := H a b.
have B := H1 a b.
Abort.
