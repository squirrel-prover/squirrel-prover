set autoIntro=false.

abstract f : message->message->message
abstract a : message
abstract b : message

system null.

equiv e : diff(f(a,b),f(a,a)).
Proof.
  fa 0.
  admit.
Qed.

equiv e2 : if diff(True,False) then diff(a,b).
Proof.
  fa 0.
  admit.
Qed.
