abstract a : message
abstract b : message

system null.

equiv _ : if diff(True,False) then diff(a,b).
Proof.
  fa 0.
  admit.
Qed.

(*------------------------------------------------------------------*)
abstract f : message -> message -> message.

equiv _ : diff(f a b,f a a).
Proof.
  fa 0.
  admit.
Qed.

(*------------------------------------------------------------------*)
abstract fT : message * message -> message.

equiv e : diff(fT(a,b),fT(a,a)).
Proof.
  fa 0.
  admit.
Qed.

(*------------------------------------------------------------------*)
global lemma _ (f : message * message -> message) : equiv (diff(f(a,b),f(a,a))).
Proof.
  fa 0.                         (* f is not ptime computable *)
  checkfail fa 0 exn Failure.
Abort.
