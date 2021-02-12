set autoIntro=false.

channel c
abstract ok : message
system (!_i in(c,x);A:out(c,ok);B:out(c,x) |
        C:out(c,ok);in(c,x);D:out(c,x)).

goal output@C = ok.
Proof.
  auto.
Qed.

goal output@D = input@D.
Proof.
  auto.
Qed.

goal forall i:index, output@B(i) = input@A(i).
Proof.
  auto.
Qed.
