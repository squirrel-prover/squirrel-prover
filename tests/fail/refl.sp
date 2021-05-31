set autoIntro=false.

channel c

abstract ok : message
abstract ko : message

system null.

equiv e : diff(ok,ko).
Proof.
  checkfail refl exn NoRefl.
Abort.

system [macros] in(c,x);out(c,x).

equiv e : if cond@A then ok.
Proof.
  checkfail refl exn NoReflMacroVar.
Abort.

equiv e : input@A.
Proof.
  checkfail refl exn NoReflMacroVar.
Abort.
