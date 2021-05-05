set autoIntro=false.

abstract a:message
abstract b:message

system null.

axiom ax : a=b.

goal assert_msg (i:message) : a=b.
Proof.
  assert (i=i) as T; 1: auto.
  by use ax.
Qed.

goal assert_cstr (i:index) : a=b.
Proof.
  assert (i=i); 1: auto.
  by use ax.
Qed.
