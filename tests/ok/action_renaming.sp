set autoIntro=false.

abstract ok : index->message
channel c

(*------------------------------------------------------------------*)
system A: !_i in(c,x);out(c,(ok(i),x)).

goal one (k:index) : happens(A(k)) => output@A(k) = (ok(k),input@A(k)).
Proof.
  auto.
Qed.

(* fail if the action does not happened *)
goal oneF (k:index) : output@A(k) = (ok(k),input@A(k)).
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
system [alt] B: !_j in(c,x); if x = ok(j) then out(c,(x,ok(j))).

goal [none,alt] two (k:index) : happens (A(k)) => output@A(k) = (input@A(k),ok(k)).
Proof.
  auto.
Qed.

(* fail if the action does not happened *)
goal [none,alt] twoF (k:index) : output@A(k) = (input@A(k),ok(k)).
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
goal [none,alt] three (k:index) : happens (A(k)) => cond@A(k) => input@A(k) = ok(k).
Proof.
  by intro k Hhap Cond; expand cond@A(k).
Qed.

(* fail if the action does not happened *)
goal [none,alt] threeF (k:index) : cond@A(k) => input@A(k) = ok(k).
Proof.
  checkfail (intro k Cond; try expand cond@A(k); auto) exn GoalNotClosed.
Abort.
