(* set debugConstr=true. *)

include Basic.

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

print system [testPrf].

(* Then, second transitivity, from testprf to testRenamed *)
system testRenamed = [testPrf] with rename equiv(diff(n_PRF,n)).


axiom [testRenamed,test2/right] tf : forall ( p, n:message), try find such that true in p else n =p .

axiom [testRenamed,test2/right] ref : forall ( n:message), diff(n,n)=n .



equiv [testRenamed,test2/right] test2.
Proof.

enrich n.
induction t.

auto.

expandall.
fa 1.
repeat fa 2.
have -> : diff(try find  such that ok = ok in n else h(ok,k),n) = n.
project.

case (try find  such that ok = ok in n else h(ok,k)); auto.
auto.
auto.


expandall.
fa 1.
repeat fa 2.

simpl. 
rewrite tf in 2.
rewrite ref in 2.
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
system testiRenamed = [testiPrf] with rename Forall (i:index), equiv(diff(n_PRF1(i),idn(i))).
(* equiv [testiPrf] t. Proof. print. admit. Qed *)


equiv [testiRenamed,testi2/right] test3.
Proof.
  enrich seq(i:index => idn(i)).
  induction t.
  
  + expandall.
    auto.
    
  + expandall.
    fa 1; repeat fa 2.
    
    have ->: try find j such that (msg(i) = msg(j) && i = j)
         in idn(j) else h(msg(i),key(i)) =
         idn(i). {
      case try find j such that (msg(i) = msg(j) && i = j)
           in idn(j) else h(msg(i),key(i)). 
      - auto.    
      - intro H2.
      destruct H2.
      by use H0 with i.
    }.
    
    have ->:  diff(idn(i),idn(i)) = idn(i).
    project; auto.
    by apply IH. 
    
    
  + expandall.
    have ->:   try find j such that (msg(i) = msg(j) && i = j)
             in idn(j) else h(msg(i),key(i)) =
             idn(i). {
      case  try find j such that (msg(i) = msg(j) && i = j)
            in idn(j) else h(msg(i),key(i)).
      - auto. 
      - intro H2.
        destruct H2.
        by use H0 with i.
    }.
    
    have ->:  diff(idn(i),idn(i)) = idn(i).
    project; auto.
    by apply IH.
Qed.

(*------------------------------------------------------------------*)
system [test_ok2] (A: out(c, <ok,<h(ok,k),h(ok2,k)>>) | B: out(c, h(ok,k))).
(* we start with a first transitivity, from test/left to testPrf *)
system test_ok2G = [test_ok2/left] with gprf, h(ok,k).

axiom [test_ok2G] ok_ok2 : ok = ok2.

goal [test_ok2G] _ :
  happens(A) =>
  ok = ok2 =>
  output@A = <ok, <n_PRF2,n_PRF2>>.
Proof.
  intro Hap ok_ok2 @/output.
  rewrite ok_ok2 /=. 
  by case (try find such that _ in n_PRF2 else _) => [_ _].
Qed.

goal [test_ok2G] _ :
  happens(A) =>
  ok <> ok2 =>
  output@A = <ok, <n_PRF2,h(ok2, k)>>.
Proof.
  intro Hap ok_ok2 @/output.
  case (try find such that (ok = ok) in n_PRF2 else _) => [_ _] //.
  case (try find such that (ok2 = ok) in n_PRF2 else _) => [_ _] //.
Qed.
