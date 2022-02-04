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
abstract ok2 : message.

system [test] (A: out(c, <ok,<h(ok,k),h(ok,k)>>) | B: out(c, h(ok,k))).

system [test2] (A: out(c, <ok,<n,n>>) | B: out(c, n)).


(*  We should have  [test/left,test2/right] *)

(* we start with a first transitivity, from test/left to testPrf *)
system testPrf = [test/left] with gprf, h(ok,k).

(* Then, second transitivity, from testprf to testRenamed *)
system testRenamed = [testPrf/left] with rename equiv(diff(n_PRF,n)).


axiom [testRenamed/left,test2/right] tf : forall ( p, n:message), try find such that true in p else n =p .

axiom [testRenamed/left,test2/right] ref : forall ( n:message), diff(n,n)=n .



equiv [testRenamed/left,test2/right] test2.
Proof.

enrich n.
induction t.

auto.

expandall.
fa 1.
repeat fa 2.
equivalent  diff(try find  such that ok = ok in n else h(ok,k),n), n.
project.

case (try find  such that ok = ok in n else h(ok,k)); auto.
auto.
auto.


expandall.
fa 1.
repeat fa 2.


equivalent ok=ok,true.
auto.
rewrite tf in 2.
rewrite ref in 2.
equivalent  diff(try find  such that ok = ok in n else h(ok,k),n), n.
project.

case (try find  such that ok = ok in n else h(ok,k)); auto.
auto.
auto.

Qed.


name key : index -> message
name idn : index -> message
name msg : index -> message

system [testi] (!_i A: out(c, <ok,h(msg(i),key(i))>) | !_i B: out(c, h(msg(i),key(i)))).

system [testi2] (!_i A: out(c, <ok, idn(i)>) | !_i B: out(c,  idn(i))).

(*  We should have  [testi/left,testi2/right] *)

(* we start with a first transitivity, from testi/left to testiPrf *)
system testiPrf = [testi/left] with gprf (j:index), h(msg(j),key(j)).

(* Then, second transitivity, from testiPrf to testiRenamed *)
system testiRenamed = [testiPrf/left] with rename forall (i:index), equiv(diff(n_PRF1(i),idn(i))).
(* equiv [testiPrf] t. Proof. print. admit. Qed *)


equiv [testiRenamed/left,testi2/right] test3.
Proof.
enrich seq(i:index-> idn(i)).
induction t.

expandall.
auto.

expandall.
fa 1. repeat fa 2.


equivalent      try find j such that (msg(i) = msg(j) && i = j)
     in idn(j) else h(msg(i),key(i)),
     idn(i).
case      try find j such that (msg(i) = msg(j) && i = j)
     in idn(j) else h(msg(i),key(i)).

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
equivalent   try find j such that (msg(i) = msg(j) && i = j)
         in idn(j) else h(msg(i),key(i)),
         idn(i).
case  try find j such that (msg(i) = msg(j) && i = j)
         in idn(j) else h(msg(i),key(i)).

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

