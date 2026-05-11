(* Same as euf_output but with output@0[b] replaced by its definition *)

hash h
name k:message
channel c

system !_a new n; out(c,h(n,k)).

lemma unforgeable (a,b:index[param]):
b <> a => h(n(b),k) <> h(n(a),k).

Proof.
  by (intro _ Heq; euf Heq).
Qed.
