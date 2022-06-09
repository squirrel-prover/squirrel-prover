

op triple (x, y, z : message) : message = <x, <y, z>>.

(* implicit return type *)
op triple' (x, y, z : message) = <x, <y, z>>.

(* generic pairs *)
abstract gpair ['a] : 'a -> 'a -> 'a.

op gtriple ['a] (x, y, z : 'a) = gpair(x, gpair(y, z)).

op foo ['a] (x : 'a) = gtriple (x,x,x).

system null.

axiom gpair_ax (x,y : message) : gpair (x,y) = <x,y>.

goal _ (a,b,c : message) : gtriple(a,b,c) = triple(a,b,c).
Proof.
  rewrite /gtriple /triple !gpair_ax. 
  auto.
Qed.
