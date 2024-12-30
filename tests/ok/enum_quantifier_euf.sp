include Core.
channel c.

name k : message.

hash h.

system null.

lemma _ : if (forall (x : message), x = empty) then empty = h(empty,k) => false.
Proof.
  intro H.
  checkfail euf H exn Failure.
Abort.

lemma _ : if (exists (x : message), x = empty) then empty = h(empty,k) => false.
Proof.
  intro H.
  checkfail euf H exn Failure.
Abort.

(*------------------------------------------------------------------*)
type E[enum].

lemma _ : if (forall (x : E), x = witness) then empty = h(empty,k) => false.
Proof.
  intro H. 
  euf H.
Qed.

(*------------------------------------------------------------------*)
type T.

lemma _ : if (forall (x : T), x = witness) then empty = h(empty,k) => false.
Proof.
  intro H. 
  checkfail euf H exn Failure.
Abort.
