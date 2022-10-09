channel c

name na : index -> message

system ((!_a out(c,na(a))) |  (in(c,m1); out(c,m1))).

goal exists_test :
  happens(A1) =>
  exists (a:index), input@A1 = na(a).
  Proof.
  intro Heq.
  exists a1.
Qed.
