set autoIntro=false.

channel c

system A : !_i new a; !_j new b; out(c,b).

global goal test (i,j,ii,jj:index) :
  [happens(A(i,j))] -> [happens(A(ii,jj))] ->
  equiv(diff(output@pred(A(i,j)),output@pred(A(ii,jj))),
        diff(output@A(i,j),output@A(ii,jj))).
Proof.
  intro *.
  expand output@A(i,j).
  expand output@A(ii,jj).
  fresh 1.
  yesif 1. 
  auto.
  admit. (* Induction hypothesis.*)
Qed.
