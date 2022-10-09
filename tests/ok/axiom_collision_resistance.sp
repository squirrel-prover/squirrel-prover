hash h
name k:message
channel c

name n : index->message

system !_a out(c,h(n(a),k)).

(* Of course, this collision resistant axiom is unsound if k is used in an other way than a key. *)

axiom collision_resistance ( ma : message, mb : message):
h(ma,k)=h(mb,k) => ma = mb.

goal unforgeable (a:index, b:index) :
  happens(A(b)) => b <> a => output@A(b) <> h(n(a),k).

Proof.
intro Hap Hneq Heq.
by use collision_resistance with n(b), n(a).
Qed.
