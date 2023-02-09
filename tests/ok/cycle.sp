hash h
name k : message
name n : message
name m : message
name t : message
channel c.

system out(c,h(n,k)).

goal collision_absurd (tau:timestamp[param]):
  output@tau <> h(m,k) &&   ( output@tau <> h(t,k) || output@tau <> h(t,k)).

Proof.
split.
cycle 1.
cycle 2.
left.
by intro Heq; euf Heq; auto.
by intro Heq; euf Heq; auto.
Qed.
