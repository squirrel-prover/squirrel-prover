(* Testing the introduction of existentials on the left,
 * manually and as part of automatic simplification. *)

abstract f : message->message
abstract a : message

system null.

axiom exists y:message, a = f(y).

goal forall (x:message),
  (exists y:message, x = f(y)) || x=f(x) =>
  (exists y:message, f(y) = x).
Proof.
  intros.
  nosimpl(case H0).
  existsleft H0.
  exists y.
  exists x.
Qed.

goal forall (x:message),
  (exists y:message, x = f(y)) || x=f(x) =>
  (exists y:message, f(y) = x).
Proof.
  intros.
  case H0.
  exists y.
  exists x.
Qed.
