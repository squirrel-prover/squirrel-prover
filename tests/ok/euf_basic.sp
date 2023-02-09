hash h
name k : message
name n : message
name m : message
channel c

system out(c,h(n,k)).

goal collision_absurd (tau:timestamp[param]) :
  happens(tau) => output@tau <> h(m,k).

Proof.
  intro Hap Heq.
  euf Heq. auto.
Qed.
