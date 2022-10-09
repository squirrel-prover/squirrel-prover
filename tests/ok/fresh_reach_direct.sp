hash h
name k : message

name n : index * index -> message

system null.

goal test (i,j:index): i <> j => h(n(i,i),k) <> n(i,j).
Proof.
 nosimpl(intro Hneq Heq).
 nosimpl(fresh Heq).
 auto.
Qed.
