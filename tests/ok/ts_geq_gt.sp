set autoIntro=false.

abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

goal _: A >= B => A > B.
Proof.
 by auto.
Qed.

goal _: A > B => A >= B.
Proof.
 intro Hgt.
undo 1.
 auto.
Qed.
