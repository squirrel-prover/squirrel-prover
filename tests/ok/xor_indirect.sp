

include Basic.

channel c

abstract ok : message.
name b : index * index -> message.

system A : !_i new a; !_j out(c,b(i,j)).

axiom len_ok (i,j:index): len(ok) = len(b(i,j)).

global goal test (i,j,ii,jj:index[const]) :
  (* [happens(A(i,j))] -> *)
  (* [happens(A(ii,jj))] -> *)
  [happens(A(i,j),A(ii,jj))] ->
  equiv(
    diff(output@pred(A(i,j)),output@pred(A(ii,jj))),
    diff(output@A(i,j),output@A(ii,jj)) XOR ok).

Proof.
  intro Hap.
  expand output@A(i,j).
  expand output@A(ii,jj). 
  xor 1.
  nosimpl(rewrite if_true in 1).
  use len_ok with ii,jj.
  by use len_ok with i,j.
  admit. (* Induction hypothesis.*)
Qed.

global goal test2 (i,j,ii,jj:index[const]) :
  [happens(A(i,j),A(ii,jj))] ->
  equiv(
    diff(output@pred(A(i,j)),output@pred(A(ii,jj))),
    ok XOR diff(output@A(i,j),output@A(ii,jj))).
Proof.
  intro Hap.
  expand output@A(i,j).
  expand output@A(ii,jj).
  xor 1, diff(b(i,j),b(ii,jj)).
  nosimpl(rewrite if_true in 1).
  by use len_ok with i,j; use len_ok with ii,jj.
  admit. (* Induction hypothesis.*)
Qed.
