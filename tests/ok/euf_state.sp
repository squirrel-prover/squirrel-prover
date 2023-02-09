hash h
name k : message
name n : message
name m : message
mutable s : message = empty

channel c

system s:= h(n,k); out(c,s).

goal collision_absurd (tau:timestamp[param]):
 happens(tau) => output@tau <> h(m,k).

Proof.
  by intro Hap Heq; euf Heq; auto.
Qed.
