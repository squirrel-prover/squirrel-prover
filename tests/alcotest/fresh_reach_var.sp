set autoIntro=false.

hash h

name n : index -> index -> message

system null.

goal test (x:message,i:index,j:index) : i <> j => h(n(i,i),x) <> n(i,j).
Proof.
 nosimpl(intro Hneq Heq).
 nosimpl(fresh Heq).
Qed.
