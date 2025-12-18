include Core.

lemma _ @system:any : 
 1 = 1.
Proof. smt. Qed.

lemma _ @system:any : 
 witness = 1.
Proof. checkfail smt exn Failure. Abort.

lemma _ @system:any : 
 "A" = "A".
Proof. smt. Qed.


lemma _ @system:any :
 witness = "A".
Proof. checkfail smt exn Failure. Abort.
