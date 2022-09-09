name n : index * index -> message

system null.

goal test (i,j:index):
i <> j => (if (exists (i':index), n(i,j) = n(i',j)) then n(i,j) else n(i,j)) <> n(i,i).
Proof.
 intro Hneq Heq.
 fresh Heq;
 constraints. 
Qed.
