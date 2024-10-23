include Core.

channel c.

system [classic] P = 
  !_i (A: out(c,empty) | B: out(c,empty)).

global theorem [P] _ (i : _[const]) :
  [happens(A i)]->
  equiv(frame@A i) ->
  equiv(
    frame@A i,
    exec@A i &&
    exists (j:index),
      B(j) < A(i) &&
      input@A i = empty &&
      input@B j = empty &&
      output@A i = empty &&
      output@B j = empty 
  ).
Proof.
 intro Hap H. 
 deduce 1.
 apply H.
Qed.

global theorem [P] _ (i : _[const]) :
  [happens(A i)]->
  equiv(frame@A i) ->
  equiv(
    frame@A i,
    (* exec@A i && *)  (* we drop exec *) 
    exists (j:index),
      B(j) < A(i) &&
      input@A i = empty &&
      input@B j = empty &&
      output@A i = empty &&
      output@B j = empty 
  ).
Proof.
 intro Hap H. 
 checkfail deduce 1 exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* same tests in a `quantum` execution model. *)


system [postquantum] PQ = 
  !_i (A: out(c,empty) | B: out(c,empty)).

open Quantum.
close Classic.

global theorem [PQ] _ (i : _[const]) :
  [happens(A i)]->
  equiv(frame@A i) ->
  equiv(
    frame@A i,
    exec@A i &&
    exists (j:index),
      B(j) < A(i) &&
      input@A i = empty &&
      input@B j = empty &&
      output@A i = empty &&
      output@B j = empty 
  ).
Proof.
 intro Hap H. 
 deduce 1.
 apply H.
Qed.

global theorem [PQ] _ (i : _[const]) :
  [happens(A i)]->
  equiv(frame@A i) ->
  equiv(
    frame@A i,
    (* exec@A i && *)  (* we drop exec *) 
    exists (j:index),
      B(j) < A(i) &&
      input@A i = empty &&
      input@B j = empty &&
      output@A i = empty &&
      output@B j = empty 
  ).
Proof.
 intro Hap H. 
 checkfail deduce 1 exn ApplyMatchFailure.
Abort.


(*------------------------------------------------------------------*)
(* use `transcript` instead of `frame` (still `quantum`) *)


global theorem [PQ] _ (i : _[const]) :
  [happens(A i)]->
  equiv(transcript@A i) ->
  equiv(
    transcript@A i,
    exec@A i &&
    exists (j:index),
      B(j) < A(i) &&
      input@A i = empty &&
      input@B j = empty &&
      output@A i = empty &&
      output@B j = empty 
  ).
Proof.
 intro Hap H. 
 deduce 1.
 apply H.
Qed.

global theorem [PQ] _ (i : _[const]) :
  [happens(A i)]->
  equiv(transcript@A i) ->
  equiv(
    transcript@A i,
    (* exec@A i && *)  (* we drop exec *) 
    exists (j:index),
      B(j) < A(i) &&
      input@A i = empty &&
      input@B j = empty &&
      output@A i = empty &&
      output@B j = empty 
  ).
Proof.
 intro Hap H. 
 checkfail deduce 1 exn ApplyMatchFailure.
Abort.
