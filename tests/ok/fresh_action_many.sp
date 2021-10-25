set autoIntro=false.

(* Test that the fresh tactic creates the correct formula when
 * several instances of the name are found in an action. *)

channel c
name n : index->message
name m : index->message
system !_i !_j out(c,<n(i),n(j)>).

global goal test (k:index) : 
  [(((exec@pred(A(k,k)) && true) => k <> k) && 
    (forall (i,j:index), A(i,j)<A(k,k) => i<>k) &&
    (forall (i,j:index), A(i,j)<A(k,k) => j<>k)) = true] ->
  [happens(A(k,k))] -> 
  equiv(frame@A(k,k)) -> 
  equiv(frame@A(k,k), diff(n(k),m(k))).
Proof. 
  intro Heq Hap H. 
  fresh 1. 
  rewrite Heq.
  nosimpl(yesif 1).
  true. 
  expandall; assumption.
Qed.
