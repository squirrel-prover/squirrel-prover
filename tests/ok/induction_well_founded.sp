(* check well-foundness for induction *)

system null.

type T.

global goal _ (x, y:message) : [x = y].
Proof. 
  induction x.                  (* WF *)
Abort.

global goal _ (x, y:timestamp) : [x = y].
Proof. 
  (* note: due to legacy tactics,
     global `induction` on `timestamp` also does a case analysis on `x`, 
     hence does not work for non-terministic `x`. 
     We use `dependent induction` instead, which does not do any
     automatic case analysis. *)
  dependent induction x.                  (* WF *)
Abort.

global goal _ (x, y:index) : [x = y].
Proof. 
  induction x.                  (* WF *)
Abort.

global goal _ (x, y:T) : [x = y].
Proof. 
  checkfail induction x exn Failure. (* not WF *)
Abort.
