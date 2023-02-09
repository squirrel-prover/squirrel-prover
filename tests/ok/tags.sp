abstract one : message.

system null.

(*------------------------------------------------------------------*)
global axiom foo (x : message[const]) : equiv(diff(x,one)).

global goal _ (x : message[const]) : equiv(diff(x,one)).
Proof. apply foo. Qed.

global goal _ (x : message) : equiv(diff(x,one)).
Proof. 
  checkfail apply foo   exn ApplyMatchFailure. 
  checkfail apply foo x exn Failure. (* proof-term failure: bad instanciation *)
Abort.

(*------------------------------------------------------------------*)
(* same with reachability atoms *)

global axiom bar (x : message[const]) : [x = one].

global goal _ (x : message[const]) : [x = one].
Proof. apply bar. Qed.

global goal _ (x : message) : [x = one].
Proof. 
  checkfail apply bar   exn Failure. (* proof-term failure: bad instanciation *)
  checkfail apply bar x exn Failure. (* proof-term failure: bad instanciation *)
Abort.

goal _ (x : message[const,glob]) : x = one.
Proof. apply bar. Qed.

goal _ (x : message) : x = one.
Proof. 
  checkfail apply bar   exn Failure. 
  checkfail apply bar x exn Failure. 
Abort.

goal _ (x : message[const]) : x = one.
Proof. 
  checkfail apply bar   exn Failure. 
  checkfail apply bar x exn Failure. 
Abort.

goal _ (x : message[glob]) : x = one.
Proof. 
  checkfail apply bar   exn Failure. 
  checkfail apply bar x exn Failure. 
Abort.
