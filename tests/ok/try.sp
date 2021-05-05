set autoIntro=false.

name k : index -> message

abstract ok : message
channel c

system !_i (
in(c,x);
try find j such that x=k(j) in
out(c,ok) else out(c,x)).

goal not_else (i:index,j:index):
 happens(A1(i)) => cond@A1(i) => output@A1(i) <> k(j).
Proof.
  intro Hap C Heq.
  expand cond@A1(i).
  by use C with j.  
Qed.
