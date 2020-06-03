channel c

name n : message

system A : !_i new a; out(c,diff(a,n)).

equiv test (i:index) :
  output@A(i).

Proof.
  expand output@A(i).
  fresh 0.
Qed.
