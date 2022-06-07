

channel c
system !_i A: in(c,x); out(c,x).

set debugConstr=true.

goal _ (i:index,j:index) :
  A(i) <= A(j) => i = j || A(i) < A(j).
Proof. 
 auto.
Qed.
