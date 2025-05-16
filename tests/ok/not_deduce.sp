include Core.
include WeakSecrecy.

system null.

global lemma permute (u,v,w0,w1:message) :
  $( (u,v) *> (w0,w1)) ->
  $( (v,u) *> (w1,w0)).
Proof.
  intro NoDed.
  apply NoDed.
Qed.

global lemma left_right_weak (u,v,w0,w1:message) :
  $( (u,v) *> (w0)) ->
  $( (u) *> (w0,w1)).
Proof.
  intro NoDed.
  apply NoDed.
Qed.

global lemma _ (u,v,w:message) :
  $( (u)   *> w ) ->
  $( (v,u) *> w ).
Proof.
  intro NoDed. 
  checkfail apply NoDed exn ApplyMatchFailure.
Abort.

global lemma _ (u,w0,w1:message) :
  $( u *> (w0, w1) ) ->
  $( u *> (w0) ).
Proof.
  intro NoDed. 
  checkfail apply NoDed exn ApplyMatchFailure.
Abort.
