hash h
name k : message
name n : message
name m : message
channel c

system out(c,h(n,k)).

goal collision_absurd :

  forall (tau:timestamp),
  output@tau <> h(m,k).

Proof.
  simpl.
  euf M0.
Qed.