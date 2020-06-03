abstract ok : message
channel c
system ((A:out(c,ok)) | (B:out(c,ok))).

goal A >= B => A > B.
Proof.
 simpl.
Qed.

goal A > B => A >= B.
Proof.
simpl.
undo 1.
simpl.
Qed.
