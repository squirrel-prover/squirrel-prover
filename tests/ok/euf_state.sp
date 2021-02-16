set autoIntro=false.

hash h
name k : message
name n : message
name m : message
mutable s : message

channel c

system s:= h(n,k); out(c,s).

goal collision_absurd (tau:timestamp):
 happens(tau) => output@tau <> h(m,k).

Proof.
  by intro tau Hap Heq; euf Heq; auto.
Qed.
