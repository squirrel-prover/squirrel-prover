hash h
name k:message
channel c

name m : message

system new n; !_a out(c,h(n,k)).

lemma unforgeable (tau:timestamp[param]):
  happens(tau) => output@tau <> h(m,k).

Proof.
  by intro Hap Heq; euf Heq.
Qed.
