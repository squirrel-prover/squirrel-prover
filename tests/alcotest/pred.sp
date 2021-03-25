set autoIntro=false.

system null.

goal _ (t:timestamp) : not (happens (init)).
Proof.
  intro t. 
Qed.
