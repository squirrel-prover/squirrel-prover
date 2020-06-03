hash h
name k : message
name n : message
name m : message
mutable s : message

channel c

system s:= h(n,k); out(c,s).

goal collision_absurd :

  forall (tau:timestamp),
  output@tau <> h(m,k).

Proof.
  simpl.
  euf M0.
Qed.
