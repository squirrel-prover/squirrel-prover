(* Test that the fresh tactic creates the correct formula when
 * several instances of the name are found in an action. *)

channel c
name n : index->message
name m : index->message
system !_i !_j out(c,<n(i),n(j)>).

include Basic.

global goal test (k:index[const]) : 
  [((exec@A(k,k) => k <> k) && 
    (forall (i,j:index), A(i,j)<A(k,k) => k<>i) &&
    (forall (i,j:index), A(i,j)<A(k,k) => k<>j)) = true] ->
  [happens(A(k,k))] -> 
  equiv(frame@A(k,k)) -> 
  equiv(frame@A(k,k), diff(n(k),m(k))).
Proof. 
  intro Heq Hap H. 
  fresh 1. 
  rewrite Heq; 1: assumption.
  expandall; assumption.
Qed.
