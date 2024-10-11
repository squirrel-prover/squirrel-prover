system S = null.

global lemma [set : S/left; equiv : S/left,S/left] toto :
  equiv(empty,fun x => diff(x,zeroes(x)), fun b => not b).
Proof.
  checkfail rewrite oracle (fun (y : message) => y) in 5 exn GoalBadShape.
  checkfail rewrite oracle empty                    in 1 exn Failure.
  checkfail rewrite oracle (fun (b : bool) => b)    in 1 exn Failure.
  checkfail rewrite oracle (fun (y : message) => y) in 0 exn Failure.
  checkfail rewrite oracle (fun (y : message) => y) in 2 exn Failure.

  rewrite oracle ~reverse (fun (y : message) => y) in 1.
  - intro f.
    admit.
  - admit.
Qed.

abstract f1 : message -> message
abstract f2 : message -> message.

global lemma [set : S/left; equiv : S/left,S/left] toto2 :
  equiv(f1, empty).
Proof.
  rewrite oracle f2 in 0.
  - admit.
  - admit.
Qed.

abstract g1 : timestamp -> bool
abstract g2 : timestamp -> bool.

global lemma [set : S/left; equiv : S/left,S/left] toto3 :
  equiv(g1, empty).
Proof.
  rewrite oracle g2 in 0.
  - admit.
  - admit.
Qed.

global lemma [set : S/left; equiv : S/left,S/left] toto4 :
  equiv(g1).
Proof.
  rewrite oracle g2 in 0.
  - admit.
  - admit.
Qed.

