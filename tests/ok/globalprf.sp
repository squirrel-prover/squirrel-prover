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


system [test] (A: out(c, <ok,h(ok,k)>) | B: out(c, h(ok,k))).

system [test2] (A: out(c, <ok,n>) | B: out(c, n)).


axiom tf :  (forall ( p, n:message),try find such that true in p else n =p ).

equiv [test/left,test2/right] test2.
Proof.
globalprf h(ok,k), ntest.
print.
rename n_PRF,n, ntest2.
print.

enrich n.
induction t.

auto.

expandall.
fa 1.
repeat fa 2.
equivalent ok=ok,true.
auto.
equivalent try find  such that true in n else h(ok,k) , n.
forceuse tf with n, h(ok,k).
auto.
equivalent diff(n,n),n.
project; auto.
auto.

expandall.
fa 1.
repeat fa 2.
equivalent ok=ok,true.
auto.
equivalent try find  such that true in n else h(ok,k) , n.
forceuse tf with n, h(ok,k).
auto.
equivalent diff(n,n),n.
project; auto.
auto.
Qed.


name key : index -> message
name idn : index -> index -> message
name msg : index -> message

system [testi] (!_i A: out(c, <ok,h(msg(i),key(i))>) | !_i B: out(c, h(msg(i),key(i)))).

system [testi2] (!_i A: out(c, <ok, idn(i,i)>) | !_i B: out(c,  idn(i,i))).

axiom tf2 :  (forall (c:boolean, p, n:message, i:index), exists i:index, c =>  try find i such that c in p else n =p ).

equiv [testi/left,testi2/right] test3.
Proof.

globalprf seq(i->h(msg(i),key(i))), ntest.
print.
rename seq(i,j -> n_PRF(i,j)),seq(i,j -> idn(i,j)), news.
print.

enrich seq(i-> idn(i,i)).
induction t.

expandall.
auto.

expandall.
fa 1. repeat fa 2.

(* TODO, the name i45 is not stable under redo operations. *)

equivalent   try find i65 such that (msg(i) = msg(i65) && i65 = i)
     in idn(i65,i) else h(msg(i),key(i)),
     idn(i,i).
case   try find i65 such that (msg(i) = msg(i65) && i65 = i)
     in idn(i65,i) else h(msg(i),key(i)).
intro H2.
destruct H2.
destruct H0.
destruct H0. auto.
intro H2.
destruct H2.
use H0 with i.
auto.

equivalent  diff(idn(i,i),idn(i,i)), idn(i,i).
project; auto.
expandseq seq(i->idn(i,i)), i.
auto.


expandall.
equivalent   try find i77 such that (msg(i) = msg(i77) && i77 = i)
         in idn(i77,i) else h(msg(i),key(i)),
         idn(i,i).
case (try find i77 such that (msg(i) = msg(i77) && i77 = i)
 in idn(i77,i) else h(msg(i),key(i))).
intro H2.
destruct H2.
destruct H0.
destruct H0. auto.
intro H2.
destruct H2.
use H0 with i.
auto.

equivalent  diff(idn(i,i),idn(i,i)), idn(i,i).
project; auto.
expandseq seq(i->idn(i,i)), i.
fa 2.
auto.

Qed.
