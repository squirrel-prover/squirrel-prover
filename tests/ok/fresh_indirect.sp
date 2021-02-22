set autoIntro=false.

channel c

system A : !_i new a; !_j new b; out(c,b).

equiv test (i,j,ii,jj:index) :
  [happens(A(i,j))] -> [happens(A(ii,jj))] ->
  diff(output@pred(A(i,j)),output@pred(A(ii,jj))),
  diff(output@A(i,j),output@A(ii,jj)).

Proof.
  intro *.
  expand output@A(i,j); 1: by auto.
  expand output@A(ii,jj); 1: by auto.
  fresh 1.
  yesif 1. 
  by auto.
  admit. (* Induction hypothesis.*)
Qed.
