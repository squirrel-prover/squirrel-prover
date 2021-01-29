channel c

abstract ok : message
name b : index->index->message

system A : !_i new a; !_j out(c,b(i,j)).

axiom len_ok : forall (i,j:index), len(ok) = len(b(i,j)).

equiv test (i,j,ii,jj:index) :
  diff(output@pred(A(i,j)),output@pred(A(ii,jj))),
  diff(output@A(i,j),output@A(ii,jj)) XOR ok.

Proof.
  expand output@A(i,j).
  expand output@A(ii,jj).
  xor 1.
  nosimpl(yesif 1).
  apply len_ok to i,j. apply len_ok to ii, jj.
  admit. (* Induction hypothesis.*)
Qed.

equiv test2 (i,j,ii,jj:index) :
  diff(output@pred(A(i,j)),output@pred(A(ii,jj))),
  ok XOR diff(output@A(i,j),output@A(ii,jj)).
Proof.
  expand output@A(i,j).
  expand output@A(ii,jj).
  xor 1, diff(b(i,j),b(ii,jj)).
  nosimpl(yesif 1).
  apply len_ok to i,j; apply len_ok to ii,jj.
  admit. (* Induction hypothesis.*)
Qed.
