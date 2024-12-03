axiom [any] r ['a] (x : 'a[adv]) : x = witness.

(* A lambda of type `message -> message` may be `adv` if its body
   is (assuming the lambda's input is computable).

   Note that we cannot have sequences over `message -> message`, as
   `message` is not `enum`. *)
lemma [any] _ : false.  
Proof.  
  have ? := r (fun (x : message) => x).
Abort.
