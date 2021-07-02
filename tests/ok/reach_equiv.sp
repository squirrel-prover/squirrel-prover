name s0 : message.
mutable s : message = s0.
channel c.
system (A: out(c,of_bool(true)) | B: out(c,of_bool(false))).

name m : message.
global axiom ax_ground : equiv(frame@pred(A),diff(s@B,m)).
global axiom [default/right,default/left] ax_ground_rev : equiv(frame@pred(A),diff(s@B,m)).
global axiom [default/left,default/left] ax_ground_left : equiv(frame@pred(A),diff(s@B,m)).

(** Dummy axioms to check that we are in a given system. *)
axiom [default/left] check_left : True.
axiom [default/right] check_right : True.

goal [default] _ : input@A = s@B => False.
Proof.
  checkfail reach_equiv ax_ground exn NoAssumpSystem.
  checkfail reach_equiv ax_ground_left exn NoAssumpSystem.
  checkfail reach_equiv ax_ground_rev exn NoAssumpSystem.
Abort.

goal [default/left] _ : input@A = s@B => False.
Proof.
  reach_equiv ax_ground_left.
  use check_left.
  fresh Meq.
Qed.

goal [default/left] _ : input@A = s@B => False.
Proof.
  reach_equiv ax_ground.
  use check_right.
  fresh Meq.
Qed.

goal [default/left] _ : input@A = s@B => False.
Proof.
  reach_equiv ax_ground_rev.
  use check_right.
  fresh Meq.
Qed.

goal [default/right] _ : input@A = s@B => False.
Proof.
  reach_equiv ax_ground.
  use check_left.
  fresh Meq.
Qed.

goal [default/right] _ : input@A = s@B => False.
Proof.
  checkfail reach_equiv ax_ground_left exn NoAssumpSystem.
  reach_equiv ax_ground_rev.
  use check_left.
  fresh Meq.
Qed.

goal [default] _ : input@A = s@B => False.
Proof.
  checkfail reach_equiv ax_ground_left exn NoAssumpSystem.
  project; reach_equiv ax_ground; fresh Meq.
Qed.

(* Same as above but without an axiom. *)

global goal [default/left,default/left] _ :
  equiv(frame@pred(A),diff(s@B,m)) -> [not(input@A = s@B)].
Proof.
  intro H.
  reach_equiv H.
  fresh Meq.
Qed.

global goal [default/left,default/right] _ :
  equiv(frame@pred(A),diff(s@B,m)) -> [not(input@A = s@B)].
Proof.
  intro H.
  checkfail reach_equiv H exn NoAssumpSystem.
  (* This time we can't project to complete the proof,
   * as projections currently drops all global hypotheses. *)
Abort.
