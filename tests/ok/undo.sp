set autoIntro=false.

system null.

goal _:True.


goal _:False.
undo 1.
Proof.
  simpl.
  undo 1.
  simpl.
Qed.
