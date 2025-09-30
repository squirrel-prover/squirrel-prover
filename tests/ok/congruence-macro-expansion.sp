(* Check that congruence closure does not fail if we first expand macros.
   This used to be a bug caused by the failure to re-use boxed terms
   created before completion when checking equalities. *)

channel c.
abstract f : message -> message.

system default =
  A:
  in(c,x);
  (* It seems important to have a try find with a condition
     that mentions the input.
     The try find must search for an index but it does not matter
     that it is unused in the condition. *)
  let m = try find _:index such that x = empty in empty in
  null.

lemma _ @system:default :
  forall (tau:timestamp),
  happens(A, tau) =>
  m@A = input@tau => f(m@A) = f(input@tau).
Proof.
  intro tau H Heq.
  congruence.
Qed.

lemma _ @system:default :
  forall (tau:timestamp),
  happens(A, tau) =>
  m@A = input@tau => f(m@A) = f(input@tau).
Proof.
  intro tau H Heq.
  expandall. 
  congruence. 
Qed.
