lemma [any] _ (j,k0,x:index):
  j < k0 => j < k0 && x <= k0 .
Proof.
  (* `auto` used to yield an anomaly here: the check below 
      is here to make sure that this is no longer the case *)
  checkfail auto exn GoalNotClosed.
Abort.
