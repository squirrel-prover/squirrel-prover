set autoIntro = false.

name s0 : message.
mutable s : message = s0.
channel c.
system (A: out(c,of_bool(true)) | B: out(c,of_bool(false))).

name m : message.
global axiom ax_ground : equiv(frame@pred(A),diff(s@B,m)).
global axiom [default/right,default/left] ax_ground_rev : equiv(frame@pred(A),diff(m,s@B)).
global axiom [default/right,default/left] ax_ground_ver : equiv(frame@pred(A),diff(s@B,m)).
global axiom [default/left,default/left] ax_ground_left : equiv(frame@pred(A),diff(s@B,m)).

(** Dummy axioms to check that we are in a given system. *)
axiom [default/left] check_left : True.
axiom [default/right] check_right : True.

goal m_fresh (tau:timestamp) : input@tau <> m.
Proof.
  intro H; by fresh H.
Qed.

goal [default] _ : happens(A) => input@A = s@B => False.
Proof.
  checkfail reach_equiv ax_ground exn NoAssumpSystem.
  checkfail reach_equiv ax_ground_left exn NoAssumpSystem.
  checkfail reach_equiv ax_ground_rev exn NoAssumpSystem.
Abort.

(* Check that timestamp atoms are not dropped by reach_equiv. *)
goal [default/left] _ (tau,tau':timestamp) : tau <= tau' => tau <= tau'.
Proof.
  reach_equiv ax_ground.
  intro H; assumption.
Qed.

goal [default/left] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  reach_equiv ax_ground_left.
  by use m_fresh with A.
Qed.

goal [default/left] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  reach_equiv ax_ground.
  use check_right.
  by use m_fresh with A.
Qed.

goal [default/left] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  reach_equiv ax_ground_rev.
  use check_right.
  by use m_fresh with A.
Qed.

goal [default/right] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  checkfail reach_equiv ax_ground_left exn NoAssumpSystem.
  reach_equiv ax_ground_ver.
  use check_left.
  by use m_fresh with A.
Qed.

goal [default] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  checkfail reach_equiv ax_ground_left exn NoAssumpSystem.
  project; [1: reach_equiv ax_ground | 2: reach_equiv ax_ground_ver];
  by use m_fresh with A.
Qed.

(* Same as above but without an axiom. *)

global goal [default/left,default/left] _ :
  [happens(A)] -> equiv(frame@pred(A),diff(s@B,m)) -> [not(input@A = s@B)].
Proof.
  intro Hap H.
  reach_equiv H.
  by use m_fresh with A.
Qed.
