

hash h

name n : index * index -> message

system null.

goal test (x:message, i,j:index[const,glob]) : i <> j => h(n(i,i),x) <> n(i,j).
Proof.
 nosimpl(intro Hneq Heq).
 fresh Heq.
Qed.
