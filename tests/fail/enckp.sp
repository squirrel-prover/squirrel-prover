

channel c

senc enc,dec

name k : message
name kbis : message
name r : message
name n : message
name m : message
abstract ok : message

name r1 : index -> message

system null.

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the key occurs in the frame. *)
equiv fail (x:message) : k,enc(n,r,diff(k,kbis)).
Proof.
  checkfail enckp 1 exn BadSSC.
Abort.
(** END TEST **)


(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the key occurs in the context. *)
equiv fail : <k,enc(n,r,diff(k,kbis))>.
Proof.
  checkfail enckp 0 exn BadSSC.
Abort.
(** END TEST **)

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the encryption is under a decryption. *)
equiv fail (x:message) : dec(enc(n,r,diff(k,kbis)),k).
Proof.
  checkfail enckp 0 exn Failure.
Abort.
(** END TEST **)


(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the random seed occurs in another action. *)
system [sharedrnd] !_i
       (out(c,<diff(n,m), enc(n,r1(i),diff(k,kbis))>) | out(c,enc(m,r1(i),diff(k,kbis)))).

equiv  [sharedrnd] test.
Proof.
enrich diff(n,m); induction t. 
by expandall; fresh 0. 

expandall. 
fa 1; fa 2; fa 2; fa 2.
checkfail enckp 2 exn SEncSharedRandom.
Abort.
(** END TEST **)

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the random seed occur in the context. *)
system  [sharedrndframe] !_i (out(c,<diff(n,m), enc(n,r1(i),diff(k,kbis))>)).
equiv  [sharedrndframe] test2.
Proof.
enrich diff(n,m). induction t. expandall. by fresh 0. 
enrich enc(m,r1(i),k). expandall. fa 2; fa 3; fa 3; fa 3.
 checkfail enckp 3 exn SEncSharedRandom.
Abort.
(** END TEST **)

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the ranodm seed is not a name. *)
system [nornd] !_i (out(c,<n, enc(n,r1(i),diff(k,kbis))>) | out(c,enc(n,ok,k))).

equiv [nornd] test3.
Proof.
enrich diff(n,m). induction t. expandall. by fresh 0. 
expandall. fa 1; fa 2; fa 2; fa 2.
checkfail enckp 3 exn SEncNoRandom.
Abort.
(** END TEST **)

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the random occurs in the context. *)
equiv test : <r,enc(n,r,diff(k,kbis))>.
Proof.
  enckp 0.
  (* the tactic succeeds, but create a non-valid reachability goal *)
Abort.
(** END TEST **)

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if the random occurs in the frame. *)
equiv test : enc(n,r,diff(k,kbis)), r.
Proof.
  enckp 0.
  (* the tactic succeeds, but create a non-valid reachability goal *)
Abort.
(** END TEST **)

(** BEGIN TEST -- AUTOMATICALLY INCLUDED IN MANUAL **)
(* Fail if there is a free message variable. *)
equiv fail (x:message) : enc(x,r,diff(k,k)).
Proof.
  checkfail enckp 0 exn BadSSC.
Abort.
(** END TEST **)
