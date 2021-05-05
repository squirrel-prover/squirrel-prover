set autoIntro=false.
system null.
axiom exists_idx : exists i:index, True.
goal absurdity : False.
Proof.
  use exists_idx.
  destruct H as [i HH].
  admit.
Qed.

goal _ (x,y,a,b : message) : <x,y> = <a,b> => x = a && y = b.
Proof.
  intro [H1 H2]. 
  split; assumption.
Qed.
