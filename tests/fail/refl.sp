

channel c

abstract ok : message
abstract ko : message

system (A: out(c,ok)).

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
