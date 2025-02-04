include Real.
open Real.

lemma _ @system:any : false <: of_int 42 + of_int 24.
Proof.
  checkfail set a := of_int 0 + _ exn Failure.
  set a := _ + _.
  rewrite /a.
Abort.
