set autoIntro=false.

abstract ok : message
abstract ko : message

system null.

equiv e : ok, ok.
Proof.
  refl.
Qed.

equiv e1 : ok.
Proof.
  refl.
Qed.

equiv e2 : diff(ok,ok).
Proof.
  refl.
Qed.

equiv e3 : diff(diff(ok,ko),ok).
Proof.
  refl.
Qed.
