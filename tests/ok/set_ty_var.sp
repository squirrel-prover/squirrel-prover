lemma foo @system:any : false.
Proof.
  (* this should fail as the type hole `_` cannot be inferred. *)
  checkfail set f := fun x : _ => x exn Failure.

  (* this succeeds *)
  set f := fun x : int => x.
Abort.
