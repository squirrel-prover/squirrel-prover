

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
  intro Hm.
  euf Hm; auto.
Qed.

goal [toto/left] _:  input@A1 <> h(ok,k).
Proof.
  intro Hm.
  euf Hm; auto.
Qed.
