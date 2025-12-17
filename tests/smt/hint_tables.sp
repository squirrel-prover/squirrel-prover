set smtSteps=10000.

abstract ok : message.
abstract a : message. 
abstract b : message. 
abstract c : message.

axiom[any] a_ok : a = ok.
axiom[any] b_ok : b = ok.
axiom[any] c_ok : c = ok.

hint smt a_ok in a.
hint smt b_ok in b.
hint smt c_ok.

lemma[any] _ : a = ok.
Proof. 
  checkfail smt exn Failure. 
  checkfail (smt hint b) exn Failure.
  checkfail (smt hint c) exn Failure. 
  smt hint a. 
Qed.

lemma[any] _ : b = ok. 
Proof. 
 smt hint a,b,c,d,default.
Qed.

lemma[any] _ : a = b.
Proof.
 checkfail smt exn Failure.
 checkfail (smt hint a) exn Failure.
 checkfail (smt hint b) exn Failure. 
 smt hint a,b.
Qed.

lemma[any] _ : c = ok && c = ok.
Proof. 
  split.
  smt hint default.
  smt.
Qed. 

 
