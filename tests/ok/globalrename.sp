set autoIntro=false.
(* set debugConstr=true. *)

hash h
name k:message
channel c
channel c2
name n:index -> message
name m:index -> message
system null.

abstract ok : message.


system [test] (!_i A: out(c, diff(n(i),m(i)) ) | (!_i B: out(c, diff(n(i),m(i)) ) )).

equiv [test] tutu.
Proof.
help.
rename seq(i:index->n(i)), seq(i:index->m(i)), newSystem.

print.
enrich seq(i:index->m(i)).
induction t.
expandall. auto.

expandall.
fa 1. fa 2. fa 2.

expandseq seq(i:index->m(i)),i.
auto.

expandall.
fa 1. fa 2. fa 2.
expandseq seq(i:index->m(i)),i.
auto.
Qed.
