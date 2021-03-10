set autoIntro=false.
system null.
axiom exists_idx : exists i:index, True.
goal absurdity : False.
Proof.
  use exists_idx.
  destruct H as [i HH].
  admit.
Qed.
