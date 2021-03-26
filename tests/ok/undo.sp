set autoIntro=false.

system null.

goal _:True.


goal _:False.
undo 1.
Proof.
  auto.
  undo 1.
  auto.
Qed.
