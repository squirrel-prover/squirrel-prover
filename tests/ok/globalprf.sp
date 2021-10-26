set autoIntro=false.
(* set debugConstr=true. *)

hash h
name k:message
channel c
channel c2
name n:message
name m:message
system null.

abstract ok : message.


system [test] (A: out(c, <ok,<h(ok,k),h(ok,k)>>) | B: out(c, h(ok,k))).

system [test2] (A: out(c, <ok,<n,n>>) | B: out(c, n)).


axiom tf :  (forall ( p, n:message),try find such that true in p else n =p ).

equiv [test/left,test2/right] test2.
Proof.
globalprf h(ok,k), ntest.
print.

rename n_PRF,n, ntest2.

enrich n.
induction t.

auto.

expandall.
fa 1.
repeat fa 2.
equivalent ok=ok,true.
auto.
equivalent try find  such that true in n else h(ok,k) , n.
admit.  (* BROKEN -> fixed with system declaration construct *)


equivalent diff(n,n),n.
project; auto.
auto.

expandall.
fa 1.
repeat fa 2.
equivalent ok=ok,true.
auto.
equivalent try find  such that true in n else h(ok,k) , n.
admit.

equivalent diff(n,n),n.
project; auto.
auto.
Qed.


name key : index -> message
name idn : index -> message
name msg : index -> message

system [testi] (!_i A: out(c, <ok,h(msg(i),key(i))>) | !_i B: out(c, h(msg(i),key(i)))).

system [testi2] (!_i A: out(c, <ok, idn(i)>) | !_i B: out(c,  idn(i))).

axiom tf2 :  (forall (c:boolean, p, n:message, i:index), exists i:index, c =>  try find i such that c in p else n =p ).

equiv [testi/left,testi2/right] test3.
Proof.

globalprf seq(i:index->h(msg(i),key(i))), ntest.
print.

rename seq(i:index -> n_PRF(i)),seq(i:index -> idn(i)), news.
print.

enrich seq(i:index-> idn(i)).
induction t.

expandall.
auto.

expandall.
fa 1. repeat fa 2.

equivalent   try find i0 such that (msg(i) = msg(i0) && i0 = i)
     in idn(i0) else h(msg(i),key(i)),
     idn(i).
case (try find i0 such that (msg(i) = msg(i0) && i0 = i)
 in idn(i0) else h(msg(i),key(i))).

intro H2.
destruct H2.
destruct H0.
destruct H0. auto.
intro H2.
destruct H2.
use H0 with i.
auto.

equivalent  diff(idn(i),idn(i)), idn(i).
project; auto.
expandseq seq(i:index->idn(i)), i.
auto.


expandall.
equivalent  try find i0 such that (msg(i) = msg(i0) && i0 = i)
         in idn(i0) else h(msg(i),key(i)),
         idn(i).
case (try find i0 such that (msg(i) = msg(i0) && i0 = i)
 in idn(i0) else h(msg(i),key(i))).

intro H2.
destruct H2.
destruct H0.
destruct H0. auto.
intro H2.
destruct H2.
use H0 with i.
auto.

equivalent  diff(idn(i),idn(i)), idn(i).
project; auto.
expandseq seq(i:index->idn(i)), i.
fa 2.
auto.

Qed.
