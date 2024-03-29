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
