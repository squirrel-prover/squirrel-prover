abstract one : message.

system null.

(*------------------------------------------------------------------*)
global axiom foo (x : message[const]) : equiv(diff(x,one)).

global lemma _ (x : message[const]) : equiv(diff(x,one)).
Proof. apply foo. Qed.

global lemma _ (x : message) : equiv(diff(x,one)).
Proof. 
  checkfail apply foo   exn ApplyMatchFailure. 
  checkfail apply foo x exn Failure. (* proof-term failure: bad instanciation *)
Abort.

(*------------------------------------------------------------------*)
(* same with reachability atoms *)

global axiom bar (x : message[const]) : [x = one].

global lemma _ (x : message[const]) : [x = one].
Proof. apply bar. Qed.

global lemma _ (x : message) : [x = one].
Proof. 
  checkfail apply bar   exn Failure. (* proof-term failure: bad instanciation *)
  checkfail apply bar x exn Failure. (* proof-term failure: bad instanciation *)
Abort.

lemma _ (x : message[const,glob]) : x = one.
Proof. apply bar. Qed.

lemma _ (x : message) : x = one.
Proof. 
  checkfail apply bar   exn Failure. 
  checkfail apply bar x exn Failure. 
Abort.

lemma _ (x : message[const]) : x = one.
Proof. 
  checkfail apply bar   exn Failure. 
  checkfail apply bar x exn Failure. 
Abort.

lemma _ (x : message[glob]) : x = one.
Proof. 
  checkfail apply bar   exn Failure. 
  checkfail apply bar x exn Failure. 
Abort.
