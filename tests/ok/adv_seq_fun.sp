axiom [any] r ['a] (x : 'a[adv]) : x = witness.

(* A lambda of type `message -> message` may be `adv` if its body
   is (assuming the lambda's input is computable).
   But a sequence over `message -> message` cannot be `adv`, as this 
   is a type of unbounded cardinal. *)
lemma [any] _ : false.  
Proof.  
  (*    *)  have ? := r (fun (x : message) => x).
  checkfail have ? := r (seq (x : message  => x)) exn Failure.
Abort.
