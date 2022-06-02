

hash h
name k:index->message
name ok:index->message
name ko:message
channel c

abstract f:message

system (!_i out(c,try find i such that false in ok(i) else f )).

name test: index -> message.
axiom dummy2: forall (j:index), ok(j)=test(j).


equiv t.
Proof.
  induction t.
  
  auto.

  expandall.
  fa 0; fa 1; fa 1.

  rewrite dummy2 in 1.
  have ->: try find i0 such that false in test(i0) else f = f. 
  by case try find i0 such that false in test(i0) else f.
  auto.
Qed.
