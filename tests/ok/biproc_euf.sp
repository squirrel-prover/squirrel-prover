name ok : message
name ko : message

channel c
name k : message

hash h

process A(res:message) = out(c,res)

system (A(h(ok,k)) | in(c,x)).

system [toto] (A(h(ko,k)) | in(c,x)).


goal test : input@A1 <> h(ko,k).
Proof.
  intros.
  euf M0.
Qed.

goal [left,toto]  input@A1 <> h(ok,k).
Proof.
  intros.
  euf M0.
Qed.
