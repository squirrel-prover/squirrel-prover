(* check parsing *)
lemma [any] _ : forall ((x,y) : message * message), x = y => False.
Proof. Abort.

(* check parsing *)
lemma [any] _ : exists ((x,y) : message * message), x = y => False.
Proof. Abort.

(* check parsing *)
op foo = fun ((x,y) : message * message) => x = y.
