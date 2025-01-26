include Core.

name a:message.
name b:message.

channel c.

process A = 
  let msg= diff(a,b) in
  out(c, msg).

process Abis = 
  let msg = diff(a,b) in
  out(c,msg).

system S1 = A.
system S2 = Abis.



global axiom [S1/left,S2/right] foo : equiv(diff(a,b)).


global lemma [S1/left,S2/right] _ :
[happens(A)] -> equiv(diff(msg@A,msg1@A),diff(a,b)).
Proof.
intro *. 
deduce 0. 
apply foo.
Qed.


global lemma [S1/left,S2/right] _ :
[happens(A)] -> equiv(diff(msg@A,msg1@A),diff(a,b)).
Proof.
intro *.
deduce 1.
apply foo.
Qed.

global lemma [S1/left,S2/right] _ :
[happens(A)] -> equiv(diff(a,b)) -> equiv(diff(msg@A,msg1@A)).
Proof.
intro *.
(* rewrite /msg /msg1 in *. *)
apply H0.
Qed.



(* global lemma [S1/left,S2/right] _ : *)
(* [happens(A)] -> equiv(diff(msg@A,msg1@A)) -> equiv(diff(a,b)). *)
(* Proof. *)
(* intro *. *)
(* deduce 0. *)
(* Abort. *)
