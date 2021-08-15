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
