channel c.
abstract m1:message.
abstract m2:message. 

system S = !_i A:out(c,m1) ; B:out(c,m2).
system P = !_i (A:out(c,m1) | C:out(c,m2)).

lemma[S] order : forall(i:index), happens(B(i)) => happens(A(i)). 
Proof. 
  smt.
Qed.

lemma[S] order2 : forall(i:index), happens(B(i)) => A(i)<B(i). 
Proof. 
  smt.
Qed.

lemma[P] disorder : forall(i:index), happens(C(i)) => happens(A(i)).
Proof.
 checkfail smt exn Failure. 
Abort.


