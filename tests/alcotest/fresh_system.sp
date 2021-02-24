set autoIntro=false.

channel c

name n : message

system A : !_i new a; out(c,diff(a,n)).

equiv test (i:index) :
  [happens(A(i))] -> output@A(i).

Proof.
  intro Hap.
  expand output@A(i).
  fresh 0.
  auto.
Qed.

