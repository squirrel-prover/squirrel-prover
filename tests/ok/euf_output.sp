hash h
name k:message
channel c

system !_a new n; out(c,h(n,k)).

lemma unforgeable (a:index, b:index):
  happens(A(b)) => b <> a => output@A(b) <> h(n(a),k).

Proof.
  intro Hap @/output Hneq Heq.
  by collision.
Qed.
