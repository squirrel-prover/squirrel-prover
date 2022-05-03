set autoIntro=false.

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

(* equiv _ : diff(ok,ok). *)
(* Proof. *)
 (* checkfail try (enrich diff(diff(ok,ko),ok)) exn ConvertionFailed. *)
(* Qed. *)

equiv _ (x : message) : x.
Proof.
  checkfail refl exn NoReflMacroVar.
Abort.
