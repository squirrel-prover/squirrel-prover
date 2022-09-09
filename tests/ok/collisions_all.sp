abstract a : message
abstract b : message
abstract c : message
hash h
name k : message
abstract x : message
abstract y : message

system null.

goal _ :
  h(a,k)=x => h(b,k)=y => y=h(c,k) => b=c.
Proof.
  intro _ _ _. 
  nosimpl(collision).
  auto.
Qed.
