
(* set debugConstr=true. *)

abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

goal _: A >= B => A > B. 
Proof.
 auto.
Qed.

goal _: A > B => A >= B.
Proof.
 auto.
Qed.

goal _: A <= B => A < B. 
Proof.
 auto.
Qed.

goal _: A < B => A <= B.
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
goal _: A >= B => happens(A,B). 
Proof.
 auto.
Qed.

goal _: A > B => happens(A,B). 
Proof.
 auto.
Qed.

goal _: A < B => happens(A,B). 
Proof.
 auto.
Qed.

goal _: A <= B => happens(A,B). 
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
(* sanity checks *)

goal _: happens(A,B) => A <= B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

goal _: happens(A,B) => A < B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

goal _: happens(A,B) => A >= B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

goal _: happens(A,B) => A > B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
