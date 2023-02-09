(** Euf Test Suite  *)

hash h
name k : message
name cst : message.

signature sign, checksign, pk

name n2 : index * index -> message.
name k1 : index -> message.


name n : message
name m : message

abstract u : message
abstract ok : message

channel c

(**************************)
(** SSC Failures checking *)
(**************************)
system null.


(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Failure when the key occurs inside the hashed message. *)
goal key_in_mess:
  h(k,k) = k => False.
Proof.
  intro Heq.
  euf Heq.
  checkfail by auto exn GoalNotClosed.
Abort.
(** END TEST **)

goal message_var :
  forall (m1: message, m2:message, m3:message),
  h(m3,k) = m1 => m3 <> m2  .
Proof.
  intro m1 m2 m3 Heq.
  checkfail euf Heq exn Failure.
Abort.

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Failure when the key occurs inside an action condition. *)
system [condSSC] in(c,x); if x=k then out(c,x).

goal [condSSC] _ (tau:timestamp[param]) :
  happens(tau) =>
  (if cond@tau then ok else zero) <> h(ok,k).
Proof.
  intro Hap Heq.
  checkfail by euf Heq exn GoalNotClosed.
Abort.
(** END TEST **)
(* k occurs in the context *)

goal _: (k = h(u,k)) => False.
Proof.
  nosimpl(intro Heq).
  checkfail by euf Heq exn GoalNotClosed.
Abort.

(* euf should not allow to conclude here, and only yeld zero=zero *)
goal _: h(zero,h(zero,k)) <> h(zero,k).
Proof.
  intro Heq.
  checkfail by nosimpl(euf Heq) exn GoalNotClosed.
Abort.


(* h and euf cannot both use the same key *)
system [joint] (out(c,h(m,k)) | ( in(c,x); if checksign(n, x, pk(k)) then out(c,x))).

goal [ joint] _ (tau:timestamp): happens(A2) => cond@A2 => False.
Proof.
  intro Hap Hcond.
  expand cond@A2.
  checkfail by euf Hcond exn GoalNotClosed.
Abort.


goal [ joint] _ (tau:timestamp): happens(A2) => output@A2<>h(m,k).
Proof.
  intro Hhap Heq.
  euf Heq; [2,3:checkfail auto exn GoalNotClosed].
Abort.

(**********************************************)
(** Check about variables naming and renaming *)
(**********************************************)

system [boundvars] out(c,seq(i,j:index => h(n2(i,j),k1(i)))).

goal [ boundvars] _ (tau:timestamp[param], j,j1,j2:index[param]):
  happens(tau) =>
  (if frame@tau = zero then ok else ok) = h(n2(j1,j2),k1(j)) => j1=j2.
Proof.
  intro Hap Heq.
  nosimpl(euf Heq). nosimpl(intro [j3 [Hle Hn]]).
  (* We should have M1: n(j,j3) = n(j1,j2), and the goal should not magically close.
     We check that j from the seq is thus indeed replaced by j3 inside this check.
  *)
Abort.

goal _ (j,j1,j2:index[param]):
  seq(i,j:index => h(n2(i,j),k1(i))) = h(n2(j1,j2),k1(j)) => j1=j2.
Proof.
  intro Hseq.
  euf Hseq. intro [j3 Hn].
  (* This should not complete the proof.
   * There should be one goal, corresponding to a possible
   * equality between n(j1,j2) and an instance of n(_,_)
   * inside the seq(_). *)
Abort.


system [dupnames] !_i out(c,<h(n,k),h(m,k)>).

goal [ dupnames] _ (tau:timestamp[param]): 
 happens(tau) => output@tau = h(u,k) => False.
Proof.
  intro Hap Heq.
  nosimpl(euf Heq).
  (* Here EUF should create two cases for action A(_). 
     There should not be a variable i1 in the second case. *)
  by intro [i [? H]]; fresh H.
  intro [i H].
  checkfail destruct H as [i1 [H HH]] exn Failure.
Abort.
