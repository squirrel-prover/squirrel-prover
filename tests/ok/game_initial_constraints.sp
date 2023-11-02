channel c.

abstract cst : message.

mutable foo (i : index) (j : index) = cst.

include Basic.

(* ========================================================= *)
system [E] null.

game LR = {
  rnd k1 : message;
  rnd k2 : message;

  oracle foo = { return diff(k1,k2) }
}

name sn1 : message.
name sn2 : message.

global lemma [E] _ : equiv(diff(sn1,sn2)).
Proof.
  crypto LR.
Qed.

global lemma [E] _ : equiv(diff(sn1,sn2)).
Proof.
  crypto LR (k1 : sn1).
Qed.

global lemma [E] _ : equiv(diff(sn1,sn2)).
Proof.
  crypto LR (k2 : sn2).
Qed.

global lemma [E] _ : equiv(diff(sn1,sn2)).
Proof.
  crypto LR (k1 : sn1) (k2 : sn2).
Qed.

global lemma [E] _ : equiv(diff(sn1,sn2)).
Proof.
  checkfail by crypto LR (k2 : sn1) exn Failure.
  checkfail by crypto LR (k1 : sn2) exn Failure.
Abort.

(* ========================================================= *)

name n1 : index -> message.
name n2 : index -> message.

abstract i0 : index.
abstract j0 : index.

(* --------------------------------------------------------- *)
global lemma [E] _ : equiv(diff(n1 i0,n2 j0)).
Proof.
  crypto LR.
Qed.

(* --------------------------------------------------------- *)
global lemma [E] _ : equiv(diff(n1 i0,n2 j0)).
Proof.
  crypto LR (k1 : n1 i0).
Qed.

(* same with a binder *)
(* global goal [E] _ : equiv(diff(n1 i0,n2 j0)). *)
(* Proof. *)
(*   by crypto LR (k1 : n1 i : i, i = i0). *)
(* Qed. *)

(* --------------------------------------------------------- *)
global lemma [E] _ : equiv(diff(n1 i0,n2 j0)).
Proof.
  by crypto LR (k2 : n2 j0).
Qed.

(* same with a binder *)
(* global goal [E] _ : equiv(diff(n1 i0,n2 j0)). *)
(* Proof. *)
(*   by crypto LR (k2 : n2 j : j, j = j0). *)
(* Qed. *)

(* --------------------------------------------------------- *)
global lemma [E] _ : equiv(diff(n1 i0,n2 j0)).
Proof.
  crypto LR (k1 : n1 i0) (k2 : n2 j0).
Qed.

(* global goal [E] _ : equiv(diff(n1 i0,n2 j0)). *)
(* Proof. *)
(*   by crypto LR (k1 : n1 i : i, i = i0) (k2 : n2 j : j, j = j0). *)
(* Qed. *)

(* --------------------------------------------------------- *)
global lemma [E] _ : equiv(diff(n1 i0,n2 j0)).
Proof.
  checkfail by crypto LR (k2 : n1 i0) exn Failure.
  (* checkfail by crypto LR (k2 : n1 i : i, i = i0) exn GoalNotClosed. *)

  checkfail by crypto LR (k1 : n2 j0) exn Failure.
  (* checkfail by crypto LR (k1 : n2 j : j, j = j0) exn GoalNotClosed. *)
Abort.
