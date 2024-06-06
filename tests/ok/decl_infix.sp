include Basic.

type T

abstract (++) : T -> T -> T.
abstract (^^) : T -> T -> T.

system null.

axiom comm (x, y, z : T): x ++ y ++ z = x ++ (y ++ z).

lemma _  (x, y, z : T) : x ++ y ++ z = x ++ (y ++ z).
Proof.
intro *.
apply comm. 
Qed.

(* --------------------------------------------------------- *)
op ( * )  x y = <x,y>.
op ( - )  x y = <x,y>.
op ( + )  x y = <x,y>.
op ( ++1+ ) x y = <x,y>.

lemma [any] _ x y : x ++1+ y = x * y && x - y = x + y.
Proof. 
  rewrite /( * ) /(+) /(-) /(++1+).
  split; auto.
Qed.
