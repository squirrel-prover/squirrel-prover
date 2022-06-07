

abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

goal _: A <= B => A < B.
Proof.
 auto.
Qed.
