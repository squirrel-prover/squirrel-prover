predicate U {P:system}  . 
predicate B {P,Q:system}. 

global axiom u {P  :system} @set:Empty @equiv:Empty : U{P}.
global axiom b {P,Q:system} @set:Empty @equiv:Empty : U{P} -> U{Q} -> B{P, Q}.

(*------------------------------------------------------------------*)
global lemma _ {P,Q:system} @set:Empty @equiv:Empty : U /\ B{P,Q}.
Proof.
  split. 
  - apply u.
  - apply b; [1: apply u{P} | 2: apply u{Q}].
Qed.
