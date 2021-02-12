set autoIntro=false.

name n : index -> index -> message

system null.

goal test :
forall (i,j:index),
i <> j => (if (exists (i':index), n(i,j) = n(i',j)) then n(i,j) else n(i,j)) <> n(i,i).
Proof.
 nosimpl(intro i j Hneq Heq).
 nosimpl(fresh Heq; intro H).
 case H. 
 auto.
Qed.
