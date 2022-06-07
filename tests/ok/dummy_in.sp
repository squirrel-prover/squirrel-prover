

channel c
abstract ok : message
system (!_i in(c,x);A:out(c,ok);B:out(c,x) |
        C:out(c,ok);in(c,x);D:out(c,x)).

goal _: happens(C) => output@C = ok.
Proof.
  auto.
Qed.

goal _: happens(D) => output@D = input@D.
Proof.
  auto.
Qed.

goal _ (i:index): happens(B(i)) => output@B(i) = input@A(i).
Proof.
 auto.
Qed.
