channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

goal forall t:timestamp,
  t = A || ((exists i:index, t = A1(i)) || t = init).
Proof.
  simpl.
  case t.
Qed.