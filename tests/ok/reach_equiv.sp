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
  checkfail rewrite equiv ax_ground exn Rewrite_equiv_system_mismatch.
  checkfail rewrite equiv ax_ground_left exn Rewrite_equiv_system_mismatch.
  checkfail rewrite equiv ax_ground_rev exn Rewrite_equiv_system_mismatch.
Abort.

(* Check that timestamp atoms are not dropped by rewrite equiv. *)
goal [default/left] _ (tau,tau':timestamp) : tau <= tau' => tau <= tau'.
Proof.
  rewrite equiv ax_ground.
  intro H; assumption.
Qed.

goal [default/left] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  rewrite equiv ax_ground_left.
  by use m_fresh with A.
Qed.

goal [default/left] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  rewrite equiv ax_ground.
  use check_right.
  by use m_fresh with A.
Qed.

goal [default/left] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  rewrite equiv -ax_ground_rev.
  use check_right.
  by use m_fresh with A.
Qed.

goal [default/right] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  checkfail rewrite equiv ax_ground_left exn Rewrite_equiv_system_mismatch.
  rewrite equiv ax_ground_ver.
  use check_left.
  by use m_fresh with A.
Qed.

goal [default] _ : happens(A) => input@A = s@B => False.
Proof.
  intro H.
  checkfail rewrite equiv ax_ground_left exn Rewrite_equiv_system_mismatch.
  project; [1: rewrite equiv ax_ground | 2: rewrite equiv ax_ground_ver];
  by use m_fresh with A.
Qed.

(* Same as above but without an axiom. *)

global goal [default/left,default/left] _ :
  [happens(A)] -> equiv(frame@pred(A),diff(s@B,m)) -> [not(input@A = s@B)].
Proof.
  intro Hap H.
  rewrite equiv H.
  by use m_fresh with A.
Qed.
