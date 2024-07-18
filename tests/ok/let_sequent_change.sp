(* There was an issue were local variables identifiers were changed
   when moving from a local sequent to a global sequent. *)

system null.

global axiom foo : [false] -> [false].

global lemma _ : 
  Let x = empty in
  [false].
Proof.
  intro x.
  have ? := foo _.
Abort.
