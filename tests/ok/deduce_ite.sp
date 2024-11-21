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
