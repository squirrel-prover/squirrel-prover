include Core.

exact axiom fooE @system:any : 1 = 0.
hint smt fooE in E.

exact lemma _ @system:any : 1 = 0.
Proof. 
  smt hint E.
Qed.

axiom fooA @system:any : 1 = 0.
hint smt fooA in A.

exact lemma _ @system:any : 1 = 0.
Proof. 
  checkfail (smt hint A) exn Failure.
Abort.
