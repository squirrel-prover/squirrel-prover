set autoIntro=false.

(* Test that the fresh tactic creates the correct formula when
 * several instances of the name are found in an action. *)

channel c
name n : index->message
name m : index->message
system !_i !_j out(c,<n(i),n(j)>).

equiv test (k:index) : 
[happens(A(k,k))] -> output@A(k,k), diff(n(k),m(k)).
Proof.
  intro Hap.
  fresh 1.
  equivalent (forall (i,j:index), A(i,j)<=A(k,k) => i<>k && j<>k), True.
    (* The equivalence does not hold. We are only checking that the right
     * formula has been produced. *)
    admit.
  nosimpl(yesif 1).
  true.
  expandall; refl.
Qed.
