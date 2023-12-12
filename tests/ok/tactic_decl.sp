(* Check that we can declare new tactics,
   and that they fail gracefully when used improperly. *)
tactic mytac = split.
lemma [any] _ : true && true.
Proof.
  mytac.
  + auto.
  + (* mytac doesn't accept arguments *)
    checkfail mytac true exn Failure.
    auto.
Qed.
