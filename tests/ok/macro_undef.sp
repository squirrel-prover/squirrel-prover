channel c.

abstract ok : message.
abstract ko : message.

system s1 =     in(c,x); let S1= ok in A : out(c, <S1, ok>).
system s2 = !_i in(c,x); let S2= ko in B : out(c, <S2, ko>).

lemma [s1] _ i: 
  happens(A, B i) => output@A = <ok,ok> && output@B i = ok.
Proof.
  intro Hap.
  split.
  + rewrite /output /S1.
    auto. 
  + checkfail rewrite /output exn Failure.
Abort.
