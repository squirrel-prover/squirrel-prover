

abstract ok : message
abstract ko : message

system null.

equiv _ : ok, ok.
Proof.
  refl.
Qed.

equiv _ : ok.
Proof.
  refl.
Qed.

equiv _ : diff(ok,ok).
Proof.
  refl.
Qed.

equiv _ (x : message) : x.
Proof.
  refl.
Qed.
