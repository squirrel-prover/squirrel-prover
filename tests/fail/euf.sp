set autoIntro=false.

(** Euf Test Suite  *)


hash h
name k:message
name cst:message

signature sign, checksign, pk

name n2 : index -> index -> message
name k1 : index -> message


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
  checkfail euf Heq exn BadSSC.
Abort.
(** END TEST **)

goal message_var :
  forall (m1: message, m2:message, m3:message),
  h(m3,k) = m1 => m3 <> m2  .
Proof.
  intro m1 m2 m3 Heq.
  checkfail euf Heq exn BadSSC.
Abort.

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Failure when the key occurs inside an action condition. *)
system [condSSC] in(c,x); if x=k then out(c,x).

goal [none,condSSC] _ (tau:timestamp) :
  happens(tau) =>
  (if cond@tau then ok else zero) <> h(ok,k).
Proof.
  intro tau Hap Heq.
  checkfail euf Heq exn BadSSC.
Abort.
(** END TEST **)
(* k occurs in the context *)

goal _: (k = h(u,k)) => False.
Proof.
  nosimpl(intro Heq).
  checkfail euf Heq exn BadSSC.
Abort.

(* euf should not allow to conclude here, and only yeld zero=zero *)
goal _: h(zero,h(zero,k)) <> h(zero,k).
Proof.
  intro Heq.
  nosimpl(euf Heq).
Abort.


(* h and euf cannot both use the same key *)
system [joint] (out(c,h(m,k)) | ( in(c,x); if checksign(x,pk(k))=n then out(c,x))).

goal [none, joint] _ (tau:timestamp): happens(A3) => cond@A3 => False.
Proof.
  intro tau Hap Hcond.
  expand cond@A3.
  checkfail euf Hcond exn BadSSC.
Abort.


goal [none, joint] _ (tau:timestamp): output@A4<>h(m,k).
Proof.
  intro tau Heq.
  checkfail euf Heq exn BadSSC.
Abort.

(**********************************************)
(** Check about variables naming and renaming *)
(**********************************************)

system [boundvars] out(c,seq(i,j -> h(n2(i,j),k1(i)))).

goal [none, boundvars] _ (tau:timestamp, j,j1,j2:index):
  happens(tau) =>
  (if cond@tau then ok else ok) = h(n2(j1,j2),k1(j)) => j1=j2.
Proof.
  intro tau j j1 j2 Hap Heq.
  nosimpl(euf Heq). nosimpl(intro Hle Hn Hj).
  (* We should have M1: n(j,j3) = n(j1,j2), and the goal should not magically close.
     We check that j from the seq is thus indeed replaced by j3 inside this check.
  *)
Abort.

goal _ (j,j1,j2:index):
  seq(i,j -> h(n2(i,j),k1(i))) = h(n2(j1,j2),k1(j)) => j1=j2.
Proof.
  intro j j1 j2 Hseq.
  euf Hseq. intro Hn Hieq.
  (* This should not complete the proof.
   * There should be one goal, corresponding to a possible
   * equality between n(j1,j2) and an instance of n(_,_)
   * inside the seq(_). *)
Abort.


system [dupnames] !_i out(c,(h(n,k),h(m,k))).

goal [none, dupnames] _ (tau:timestamp): 
 happens(tau) => output@tau = h(u,k) => False.
Proof.
  intro tau Hap Heq.
  nosimpl(euf Heq).
  (* Here EUF should create two cases for action A(_).
   * In each case a fresh index variable i should be created;
   * there should not be a second index variable i1 in the
   * second case. *)
  by auto.
  checkfail assert (i1=i1) exn CannotConvert.
Abort.
