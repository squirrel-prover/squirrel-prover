hash h
name k:message
channel c

name n : index->message

(* TODO having a new n under the ! should be equivalent;
        it does not seem to be the case at the moment *)

system !_a out(c,h(n(a),k)).

goal unforgeable :
  forall (a:index, b:index),
  b <> a =>
  output@A(b) <> h(n(a),k).

Proof.
  simpl.
  collision.
Qed.