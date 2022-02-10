set autoIntro=false.

hash h (1)
name k : message

abstract a : message
abstract b : message

system null.

goal _ (i,j:index) : h(i,a,k) = h(j,b,k) => a = b.
Proof.
  nosimpl(intro Heq).
  checkfail collision exn NoCollision.
Qed.
