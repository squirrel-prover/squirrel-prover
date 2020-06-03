name n : index -> index -> message

system null.

goal test :
forall (i,j:index),
i <> j => (if (exists (i':index), n(i,j) = n(i',j)) then n(i,j) else n(i,j)) <> n(i,i).
Proof.
 nosimpl(intros).
 nosimpl(fresh M0).
 constraints.
 constraints.
Qed.
