include Core.
include WeakSecrecy.

global lemma _ 
  @system:any
   phi (u : message) (f : _ -> message[adv])
:
  $( (phi,if phi then u) |> (if phi then f u)).
Proof.
  deduce ~all.
Qed.

(* same goal, without the condition `phi` *)
global lemma _ 
  @system:any
   phi (u : message) (f : _ -> message[adv])
:
  $( (if phi then u) |> (if phi then f u)).
Proof.
  checkfail (deduce ~all) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
global lemma _ 
  @system:any
   phi (u : _ -> message) (f : _ -> message[adv])
:
  $(
     (fun i:index => phi i, 
      fun i:index => if phi i then u i) 
     |>
     (fun i:index => (if phi i then f (u i)))
   ).
Proof.
  deduce ~all.
Qed.

(* same goal but having `phi : _[adv]` instead of as an input *)
global lemma _ 
  @system:any
   (phi : _[adv]) (u : _ -> message) (f : _ -> message[adv])
:
  $(
     (fun i:index => if phi i then u i) 
     |>
     (fun i:index => (if phi i then f (u i)))
   ).
Proof.
  deduce ~all.
Qed.

(* same goal without being able to compute `phi` *)
global lemma _ 
  @system:any
   (phi : _) (u : _ -> message) (f : _ -> message[adv])
:
  $(
     (fun i:index => if phi i then u i) 
     |>
     (fun i:index => (if phi i then f (u i)))
   ).
Proof.
  checkfail (deduce ~all) exn ApplyMatchFailure.
Abort.
