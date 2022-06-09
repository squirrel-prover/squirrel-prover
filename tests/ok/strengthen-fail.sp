

channel c.

name na : message

abstract ok : message.
abstract ko : message.

process P(i : index) = 
  in(c,x);
  if na = x then  (* non-trivial test, so that cond@t and exec@t are non-trivial. *)
    out(c,ok) 
  else 
    out(c, ko).

system !_i P(i).


(* check that frame strenghtening does not deduce cond@t from frame@t *)
global goal _ (t :timestamp) :
  [happens(t)] -> 
  equiv(frame@t) -> equiv(frame@t, cond@t).
Proof. 
  checkfail (intro _ H; apply H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* check that frame@t -> exec@t *)

global goal _ (t :timestamp) :
  [happens(t)] ->
  equiv(frame@t) -> equiv(frame@t, exec@t).
Proof. 
  intro _ H; apply H.
Qed.

