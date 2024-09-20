(* Test projections for set annotations in proof terms.
   This file is incomplete; some variants have not been included
   because they do not currently pass. *)

system S1 = null.
system S2 = null.

(* ---------------------------------------- *)

abstract p1 : bool.
abstract p2 : bool.
abstract q1 : bool.
abstract q2 : bool.

global axiom [S1] ax1 : [diff(p1,p2)] -> [diff(q1,q2)].
global axiom [S1] ax2 : [diff(p1,p2)].

local lemma [S1/left] pass_1 : q1.
Proof.
  apply ax1 ax2.
Qed.

global lemma [set:S1/left; equiv:Empty] fail_1 : [q1].
Proof.
  (* Proof term construction should break, since it is not
     possible to project ax1 to [S1/left].
     In the future, instead of failing, we could produce a subgoal
     requiring to prove [diff(p1,p2)] wrt [S1/left,S1/right]. *)
  checkfail apply (ax1 _) exn Failure.
Abort.

global lemma [set:S1/left; equiv:Empty] fail_2 : [q1].
Proof.
  (* A failure is expected here as ax1 cannot be projected to the
     current system annotation. The possible improvement noted in
     fail_1 seems difficult to achieve here, as it would not be
     local to the proof term construction. *)
  checkfail apply ax1 exn Failure.
Abort.

(* Local variant of fail_1. *)
local lemma [S1/left] fail_1_local : q1.
Proof.
  checkfail apply (ax1 _) exn Failure.
Abort.

(* Local variant of fail_2. *)
local lemma [S1/left] fail_2_local : q1.
Proof.
  checkfail apply ax1 exn Failure.
Abort.

(* ---------------------------------------- *)

(* Variants where local formulas are system-independent,
   enabling the projections that were previously impossible. *)

abstract p : bool.
abstract q : bool.

global axiom [S1] ax1' : [p] -> [q].
global axiom [S1] ax2' : [p].

global lemma [set:S1/left; equiv:Empty] _ : [q].
Proof.
  apply ax1' ax2'.
Qed.

global lemma [set:S1/left; equiv:Empty] _ : [q].
Proof.
  apply ax1' _.
  apply ax2'.
Qed.

global lemma [set:S1/left; equiv:Empty] _ : [q].
Proof.
  apply ax1'.
  apply ax2'.
Qed.

local lemma [S1/left] _ : q.
Proof.
  apply ax1' ax2'.
Qed.

local lemma [S1/left] _ : q.
Proof.
  apply ax1' _.
  apply ax2'.
Qed.

local lemma [S1/left] _ : q.
Proof.
  apply ax1'.
  apply ax2'.
Qed.
