set autoIntro=false.

hash h
name k : message
name n : message
name m : message
channel c

system out(c,h(n,k)).

goal collision_absurd (tau:timestamp) :
  happens(tau) => output@tau <> h(m,k).

Proof.
  intro tau Hap Heq.
  euf Heq. by auto.
Qed.
