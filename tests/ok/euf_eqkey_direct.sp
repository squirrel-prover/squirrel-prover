

(* Check that equality constraints on key indices are properly obtained
 * for direct cases. *)

hash h
name n : message
name k : index * index -> message

system null.

goal _ (a,b,i:index[param]):
  h(n,k(i,i)) = h(n,k(a,b)) =>
  a = b.
Proof.
  intro Heq.
  euf Heq. 
  (* There should be one direct case,
   * where index i should be equal to both a and b. *)
  intro [_ _]; auto.
Qed.
