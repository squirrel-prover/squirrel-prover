

abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

lemma _: A <= B => A < B.
Proof.
 auto.
Qed.
