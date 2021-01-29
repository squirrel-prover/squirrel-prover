hash h
name k : message
name n : message
name m : message
channel c

system out(c,n).

goal collision_absurd :

  forall (tau:timestamp),
  output@tau <> h(m,k).

Proof.
  by intro tau Heq; euf Heq; auto.
Qed.
