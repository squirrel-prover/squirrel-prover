(* check well-foundness for induction *)

system null.

type T.

global lemma _ (x, y:message[const]) : [x = y].
Proof. 
  induction x.                  (* WF *)
Abort.

global lemma _ (x, y:timestamp[const]) : [x = y].
Proof.
  dependent induction x.                  (* WF *)
Abort.

global lemma _ (x, y:index[const]) : [x = y].
Proof. 
  induction x.                  (* WF *)
Abort.

global lemma _ (x:index[const]) (y:index) : [x = y].
Proof.
  induction x.                  (* y does not need to be const *)
Abort.

global lemma _ (x, y:timestamp) : [x = y].
Proof.
  checkfail dependent induction x exn Failure.                  (* not const*)
Abort.

global lemma _ (x, y: index) : [x = y].
Proof.
  checkfail dependent induction x exn Failure.                  (* not const*)
Abort.

global lemma _ (x, y:index) : [x = y].
Proof.
  checkfail induction x exn Failure.                  (* not const *)
Abort.

global lemma _ (x, y:T) : [x = y].
Proof. 
  checkfail induction x exn Failure. (* not WF *)
Abort.
