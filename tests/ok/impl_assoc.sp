set autoIntro=false.

system null.

goal _ (i:index,j:index):
  i=j => i=j => i=j.
Proof.
 by auto.
Qed.
