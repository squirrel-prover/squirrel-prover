hash h
name k:message
channel c

name n : index->message

(* Of course, this collision resistant axiom is unsound if k is used in an other way than a key. *)

axiom collision_resistance :
forall ( ma : message, mb : message),
h(ma,k)=h(mb,k) => ma = mb

system !_a out(c,h(n(a),k)).

goal unforgeable :
  forall (a:index, b:index),
  (b <> a =>
  output@A(b) <> h(n(a),k)).

Proof.
simpl.
apply collision_resistance to
    n(b),
   n(a).
Qed.