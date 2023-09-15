

hash h
name k : message
name n : message
name m : message
channel c

system out(c,n).

lemma collision_absurd (tau:timestamp[param]):
 happens(tau) => output@tau <> h(m,k).

Proof.
  by intro Hap Heq; euf Heq; auto.
Qed.
