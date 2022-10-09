(* check parsing *)
goal [any] _ : forall ((x,y) : message * message), x = y => False.
Proof. Abort.

(* check parsing *)
goal [any] _ : exists ((x,y) : message * message), x = y => False.
Proof. Abort.

(* check parsing *)
op foo = fun ((x,y) : message * message) => x = y.
