channel c
name n : index->message
system !_i in(c,x);out(c,x).

goal : forall (i,j:index)
  happens(A(i),A(j)) => A(i) = A(j) => n(i) = n(j).
Proof. smt.
  (* nosimpl(intro * ). *)
  (* nosimpl assert (i=j). *)
  (* nosimpl constraints. *)
  (* nosimpl congruence. *)
Qed.
