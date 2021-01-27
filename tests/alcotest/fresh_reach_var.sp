hash h

name n : index -> index -> message

system null.

goal test :
 forall (x:message,i:index,j:index), i <> j => h(n(i,i),x) <> n(i,j).
Proof.
 nosimpl(intros).
 nosimpl(fresh H0).
 case H0.
Qed.
