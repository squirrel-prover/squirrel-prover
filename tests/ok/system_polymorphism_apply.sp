predicate U {P}  . 
predicate B {P Q}. 

global axiom u {P  } in [set:Empty; equiv:Empty] : U{[P]}.
global axiom b {P Q} in [set:Empty; equiv:Empty] : U{[P]} -> U{[Q]} -> B{[P] [Q]}.

(*------------------------------------------------------------------*)
global lemma _ {P Q} in [set:Empty; equiv:Empty] : U /\ B{[P] [Q]}.
Proof.
  split. 
  - apply u.
  - apply b; [1: apply u{[P]} | 2: apply u{[Q]}].
Qed.
