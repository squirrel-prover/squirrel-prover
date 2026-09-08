include Core.
include NonDeduction.
include Int.
open Int.

(* Indices axiomatisation library *)
include[admit] "indices.sp". 

(* DH library *)
include[admit] "DHLib.sp".

(* Protocol model + Healthy/Sync/Safe predicates *)
include[admit] "model.sp".

(* Simple lemmas that does not depend on the protocol *)
include[admit] "utils.sp".

(* Helping lemmas concerning some trace properties *)
include[admit] "trace.sp".

(* Non-collision lemmas *)
include[admit] "non_collision.sp".

(* Definitions of the oracles used in the secrecy proof *)
include[admit] "oracles.sp".


(* Simulation proof: oracles |> frame *)
include[admit] "simulation.sp".

(* Secrecy proof: oracles *> secrets *)
include[admit] "secrecy_p1.sp".
include[admit] "secrecy_p2.sp".
include[admit] "secrecy_p3.sp".

(* Final lemma: frame *> secrets *)
global lemma PCS_R @set:S/left (tau: timestamp[const], i:index [const]):
  [happens(tau, R i)] ->
   [  HealthyR i] ->
      $( (frame@tau) *> (RKRsend@R i) ).
Proof.
  intro Ord Hap.

  (* Replace the frame@tau by our oracles set *)
  have Ded := DeduceFrame tau tau _; [1:auto].
  deduce with Ded; clear Ded.

  (* Conclude with the general secrecy lemma. *)
  have S := Secret_base tau (R i) 4 Ord. 
  rewrite /Secret_prop /Secret_target in S.
  have SecretR := S _ i i _; [2:constraints] => {S} //.
Qed.

global lemma PCS_I @set:S/left (tau: timestamp[const], i:index [const]):
  [happens(tau, I i)] ->
   [  HealthyI i] ->
      $( (frame@tau) *> (RKIsend@I i) ).
Proof.
  intro Ord Hap.

  (* Replace the frame@tau by our oracles set *)
  have Ded := DeduceFrame tau tau _; [1:auto].
  deduce with Ded; clear Ded.

  (* Conclude with the general secrecy lemma. *)
  have S := Secret_base tau (I i) 3 Ord. 
  rewrite /Secret_prop /Secret_target in S.
  have SecretI := S _ i i _; [2:constraints] => {S} //.
Qed.


(* Also, we remark that PCS is a generalization of forward secrecy.
   If we have no compromise before a timepoint, then we are looking at
   an healthy state, and can conclude with PCS. *) 
global lemma FS_R @set:S/left (tau: timestamp[const], i:index [const]):
  [happens(tau, R i)] ->
   [(forall j, (j ~< i || j=i) => safeI j && safeR j) ] ->
      $( (frame@tau) *> (RKRsend@R i) ).
Proof.
  intro Ord Safe.

  have [H _] := healthy_from_safe (i, false) _. by simpl.
  simpl.

  by apply PCS_R. 
Qed.


global lemma FS_I @set:S/left (tau: timestamp[const], i:index [const]):
  [happens(tau, I i)] ->
   [(forall j, (j ~< i || j=i) => safeI j && safeR j) ] ->
      $( (frame@tau) *> (RKIsend@I i) ).
Proof.
  intro Ord Safe.

  have [_ H] := healthy_from_safe (i, true) _. by simpl.
  simpl.

  by apply PCS_I. 
Qed.
