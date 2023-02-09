

(* Same as euf_output but with output@0[b] replaced by its definition *)

hash h
name k:message
channel c

name n : index->message

(* TODO having a new n under the ! should be equivalent;
        it does not seem to be the case at the moment *)

system !_a out(c,h(n(a),k)).

goal unforgeable (a,b:index[param]):
b <> a => h(n(b),k) <> h(n(a),k).

Proof.
  by (intro _ Heq; euf Heq).
Qed.
