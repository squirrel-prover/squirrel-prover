system P = null.

(* --------------------------------------------------------- *)

game A = {
  oracle o = {
    var x = diff(0,1);
    x := diff(1,0);
    return x;
  }
}.

global lemma _ @system:P : equiv(diff(1,0)).
Proof.
  crypto A.
Qed.

global lemma _ @system:P : equiv(diff(0,1)).
Proof.
  checkfail crypto A exn Failure.
Abort.

(* --------------------------------------------------------- *)
game B = {
  oracle o = {
    var x = diff(0,1);
    x := diff(1,0);
    x := diff(0,1);
    return x;
  }
}.

global lemma _ @system:P : equiv(diff(1,0)).
Proof.
  checkfail crypto B exn Failure.
Abort.

global lemma _ @system:P : equiv(diff(0,1)).
Proof.
  crypto B.
Qed.

(* --------------------------------------------------------- *)

game C = {
  oracle o = {
    var x = (0,diff(0,1));
    x := (diff(1,0),x#2);
    return x;
  }
}.

global lemma _ @system:P : equiv((diff(1,0),diff(0,1))).
Proof.
  crypto C.
Qed.

(* --------------------------------------------------------- *)

game D = {
  oracle o = {
    var x = 0;
    var y = 1;
    x := diff(x,y);
    return x;
  }
}.

global lemma _ @system:P : equiv(diff(0,1)).
Proof.
  crypto D.
Qed.

global lemma _ @system:P : equiv(diff(1,0)).
Proof.
  checkfail crypto D exn Failure.
Abort.

