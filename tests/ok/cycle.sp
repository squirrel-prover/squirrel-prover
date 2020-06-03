hash h
name k : message
name n : message
name m : message
name t : message
channel c

system out(c,h(n,k)).

goal collision_absurd :

  forall (tau:timestamp),
  output@tau <> h(m,k) &&   ( output@tau <> h(t,k) || output@tau <> h(t,k)).

Proof.
simpl.
split.
cycle 1.
cycle 2.
left.
euf M0.
euf M0.
Qed.
