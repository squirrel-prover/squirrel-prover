set autoIntro=false.

system null.

axiom toto : diff(true,false) = true.

axiom tutu : false = true.

goal [default/right] _ : false = true.
Proof.
  by rewrite tutu. 
Qed.

goal [default/right] _ : false = true.
Proof.
  checkfail rewrite toto exn NothingToRewrite.
Abort.
