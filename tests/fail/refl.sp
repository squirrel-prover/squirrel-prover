channel c

abstract ok : message
abstract ko : message

system null.

equiv e : diff(ok,ko).
Proof.
  checkfail refl with NoRefl.
Abort.

system [macros] in(c,x);out(c,x).

equiv e : if cond@A then ok.
Proof.
  checkfail refl with NoReflMacros.
Abort.

equiv e : input@A.
Proof.
  checkfail refl with NoReflMacros.
Abort.
