
(* set debugConstr=true. *)

abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

lemma _: A >= B => A > B. 
Proof.
 auto.
Qed.

lemma _: A > B => A >= B.
Proof.
 auto.
Qed.

lemma _: A <= B => A < B. 
Proof.
 auto.
Qed.

lemma _: A < B => A <= B.
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
lemma _: A >= B => happens(A,B). 
Proof.
 auto.
Qed.

lemma _: A > B => happens(A,B). 
Proof.
 auto.
Qed.

lemma _: A < B => happens(A,B). 
Proof.
 auto.
Qed.

lemma _: A <= B => happens(A,B). 
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
(* sanity checks *)

lemma _: happens(A,B) => A <= B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

lemma _: happens(A,B) => A < B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

lemma _: happens(A,B) => A >= B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

lemma _: happens(A,B) => A > B. 
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
