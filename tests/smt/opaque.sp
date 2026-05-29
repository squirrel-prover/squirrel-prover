op p : message -> message.

(* ----------------------------------------------------------------- *)
let rec f ~opaque (x : message) : message = 
  if x = empty then empty else f (p x).
Proof. admit. Qed.

lemma _ @system:any (x : message) : 
  f x = if x = empty then empty else f (p x).
Proof. 
  reduce ~macro. (* if `f` was not `opaque`, this would not terminate *)
Abort.

(* ----------------------------------------------------------------- *)
let rec g ~opaque (x : message) : message = 
  if x = empty then empty else h x

and h ~opaque x = g (p x).
Proof. admit. Qed.

lemma _ @system:any (x : message) : 
  g x = if x = empty then empty else h x.
Proof. 
  reduce ~macro. 
  checkfail (smt ~steps:10000 ~no_macros) exn Failure.
Abort.

lemma _ @system:any (x : message) : 
  h x = g (p x).
Proof. 
  reduce ~macro. 
  checkfail (smt ~steps:10000 ~no_macros) exn Failure.
Abort.
