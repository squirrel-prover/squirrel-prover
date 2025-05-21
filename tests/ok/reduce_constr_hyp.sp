include Core. 

lemma _ @system:any t : happens(t) => true. 
Proof. 
  intro H. 
  rewrite `[/= ~constr]. 
  have B := H.                  (* ensure that `B` has not been cleared. *)
  true.
Qed.
