set autoIntro=false.

(* Test that the prf tactic creates the correct formula when
 * several instances of the name are found in an action. *)

channel c
hash h
name k : message
name n : index->message
name m : index->message
system !_i !_j out(c,h(<n(i),n(j)>,k)).

equiv test (i:index) : 
[happens(A(i,i))] -> output@A(i,i), diff(h(n(i),k),h(m(i),k)).
Proof.
  intro Hap.
  prf 1.
  equivalent
    (forall (i1,j:index),
      diff((A(i1,j) <= A(i,i) => n(i) <> <n(i1),n(j)>),
           (A(i1,j) <= A(i,i) => m(i) <> <n(i1),n(j)>))),
    True.
    (* The equivalence does not hold. We are only checking that the right
     * formula has been produced. *)
  admit.
  yesif 1.
Qed.
