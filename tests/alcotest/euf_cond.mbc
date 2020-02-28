hash h
name k : message
abstract ok : message
channel c
system in(c,x); if x=k then out(c,x).

goal forall tau:timestamp,
  (if cond@tau then ok else zero) <> h(ok,k).
Proof.
  intros.
  euf M0.
