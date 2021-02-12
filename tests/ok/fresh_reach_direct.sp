set autoIntro=false.

hash h
name k : message

name n : index -> index -> message

system null.

goal test :
 forall (i,j:index), i <> j => h(n(i,i),k) <> n(i,j).
Proof.
 nosimpl(intro i j Hneq Heq).
 nosimpl(fresh Heq).
 auto.
Qed.
