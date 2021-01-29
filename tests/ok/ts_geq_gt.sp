abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

goal A >= B => A > B.
Proof.
 by auto.
Qed.

goal A > B => A >= B.
Proof.
 intro Hgt.
undo 1.
 auto.
Qed.
