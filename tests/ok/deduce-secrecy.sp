include Core.
include WeakSecrecy.

system P = null.


global lemma[set:P/left; equiv:none] _:
  $((empty, empty) |> (zero)).
Proof.
  deduce ~right.
Qed.

global lemma[set:P/left; equiv:P/left,P/left] _:
  $((empty, empty) |> (zero)).
Proof.
  deduce ~left.
  deduce. 
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau, frame@tau) |> (exec@tau)).
Proof.
  deduce ~right 0.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau, frame@tau) |> (exec@tau)).
Proof.
  deduce ~left 0.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau) |> (frame@(pred tau))).
Proof.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  [exec@tau] -> $((frame@tau) |> (output@tau)).
Proof.
  intro H.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau) |> (output@tau)).
Proof. 
  checkfail (deduce ~all) exn ApplyMatchFailure.
Abort.

global lemma [any] _ (tau : timestamp[const]):
  [happens tau] -> [exec@tau] ->
  $(zero |> zero).
Proof.
  intro Hap E.
  deduce.
Qed.

(*------------------------------------------------------------------*)
(* deduce modulo reduction *)

(* macros are reduced *)
global lemma[set:P/left; equiv:none] _:
  [happens(init)] -> $(empty |> (frame@init,exec@init)).
Proof.
  intro H.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _:
  $(empty |> (frame@init,exec@init)).
Proof.
  checkfail (deduce ~all) exn ApplyMatchFailure.
Abort.

op a : message.
op b = a.

(* operators are reduced *)
global lemma[set:P/left; equiv:none] _:
  $(a |> b).
Proof.
  deduce.
Qed.

(* in an arbitrary system *)
global lemma [any] _:
  $(a |> b).
Proof.
  deduce.
Qed.

(* operators are reduced *)
global lemma[set:P/left; equiv:none] _:
  Let x = b in
  $(a |> x).
Proof.
  intro x.
  deduce.
Qed.

(*------------------------------------------------------------------*)

global lemma [any] _ (x,x0,y,z : message) (f : _ -> message[adv]):
  $(x |> x0) -> $(x |> (z,y)) -> $(x |> (x0,z,f y)).
Proof.
  intro A H.
  checkfail (deduce ~all) exn ApplyMatchFailure.
  deduce with H.
  assumption A.
Qed.

global lemma [any] _ (x,x0,y,z,w : message) (f : _ -> message[adv]):
  $(x |> (w, x0)) -> $((x,x0) |> (z,y)) -> $(x |> (z,f y,w)).
Proof.
  intro A H.
  checkfail (deduce ~all) exn ApplyMatchFailure.
  deduce with H.
  assumption A.
Qed.

global lemma _ 
  {P:system[pair]} @set:P @equiv:P
  (x,x0,y,z : message) (f : _ -> message[adv])
:
  equiv(x,x0) -> $((x,x0) |> (z,y)) -> equiv(x,z,f y).
Proof.
  intro A H.
  deduce with H.
  assumption A.
Qed.

(*------------------------------------------------------------------*)
(* tests `deduce with` with proof-terms *)

op u : message.
op v : message.

global lemma _ 
  {P:system[pair]} @set:P @equiv:P
  (x,x0,y,z : message) (f : _ -> message[adv])
:
  equiv(x,x0) -> [u=v] -> ([u=v] -> $((x,x0) |> (z,y))) -> equiv(x,z,f y).
Proof.
  intro A B H.
  checkfail deduce with H exn Failure. (* must discharge [u=v] *)
  deduce with H _.
  + assumption B.
  + assumption A.
Qed.

global lemma _ 
  {P:system[pair]} @set:P @equiv:P
  (x,x0,y,z : message) (f : _ -> message[adv])
:
  equiv(x,x0) -> (Forall (_ : message), $((x,x0) |> (z,y))) -> equiv(x,z,f y).
Proof.
  intro A H.
  checkfail deduce with H exn Failure. (* must provide a value for `_` *) 
  checkfail deduce with H _ exn CannotInferPats. (* cannot infer `_` automatically *)
  deduce with H empty.
  assumption A.
Qed.



op f : message -> message
op g : message -> message. 
op w:message.

global lemma _ @set:P :
 (Forall (x:message), $(u |> (f x))) ->
 (Forall (x:message), $(u |> (g x))) ->
 $(u |> (f v, g w) ).
Proof.
  intro H H'.
  deduce ~right 0.
  deduce.
Qed.
