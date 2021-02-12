set autoIntro=false.

abstract a:message
abstract b:message

system null.

axiom ax : a=b.

goal assert_msg : forall (i:message), a=b.
Proof.
  intro i.
  assert (i=i).
  apply ax.
Qed.

goal assert_cstr : forall (i:index), a=b.
Proof.
  intro i.
  assert (i=i).
  apply ax.
Qed.
