set autoIntro=false.

channel c

name n : message

system A : !_i new a; out(c,diff(a,n)).

global goal test (i, j:index) :
  [happens(A(i), A(j))] -> equiv(output@A(i),output@A(j)).
Proof.
  intro Hap.  
  rewrite /output.
  fresh 0.
  fresh 1.
  auto.
Qed.

