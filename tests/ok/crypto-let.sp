
include Core.

name a:message.
name b:message.

channel c.

(*------------------------------------------------------------------*)
system B1 = out(c, diff(a,b)).
system B2 = out(c, diff(a,b)). (* same process *)

game FOO = {
   oracle foo = {
    rnd a:message;
    rnd b:message;
    return diff(a,b)}
}.

global lemma [B1/left,B2/right] _ (t:timestamp[const]) : 
[happens(t)] -> 
equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
Qed.

global lemma [B1/left,B2/right] _ (t:timestamp[const]) :
[happens(t)] ->
equiv(diff(a,b),frame@t).
Proof.
intro *.
crypto FOO => //.
Qed.

(*------------------------------------------------------------------*)
process A = 
  let msg= diff(a,b) in
  out(c, msg).

system S1= A.
system S2= A.

(* TODO: for now, crypto does not handle well cross-system application *)
(* global lemma [S1/left,S2/right] _ (t:timestamp[const]) :  *)
(* [happens(t)] ->  *)
(* equiv(frame@t). *)
(* Proof. *)
(* intro *. *)
(* crypto FOO => //. *)
(* Qed. *)
