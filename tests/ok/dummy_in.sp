

channel c
abstract ok : message
system (!_i in(c,x);A:out(c,ok);B:out(c,x) |
        C:out(c,ok);in(c,x);D:out(c,x)).

lemma _: happens(C) => output@C = ok.
Proof.
  auto.
Qed.

lemma _: happens(D) => output@D = input@D.
Proof.
  auto.
Qed.

lemma _ (i:index): happens(B(i)) => output@B(i) = input@A(i).
Proof.
 auto.
Qed.
