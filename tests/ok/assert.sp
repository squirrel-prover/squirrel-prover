abstract a:message
abstract b:message

axiom ax : a=b

system null.

goal assert_msg : forall (i:message), a=b.
Proof.
  simpl.
  assert (i=i).
  apply ax.
Qed.

goal assert_cstr : forall (i:index), a=b.
Proof.
  simpl.
  assert (i=i).
  apply ax.
Qed.
