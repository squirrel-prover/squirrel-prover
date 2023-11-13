include Basic.

system null.

global lemma _ (i : index) j : [i <> j] -> [false].
Proof.
  intro H.
  case (i = j); 2:admit.
  nosimpl intro A.
  checkfail rewrite A in H exn NothingToRewrite. 
  simpl.  
  localize H as H0.
  rewrite A in H0.
  auto.
Qed.

