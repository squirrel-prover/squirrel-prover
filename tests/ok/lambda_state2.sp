mutable f (i:index): message -> message * index = fun (x : message) => (x, i).

channel c.

process A(i : index) =
  in(c,m);
  f(i) := fun (x : message) => (<x,m>,i);
  out(c,empty).

system !_i A(i).

goal _ (i : index) :
  happens(A(i)) =>
  f(i)@A(i) = fun (x : message) => (<x, input@A(i)>,i).
Proof. 
  rewrite /f /=. 
  auto. 
Qed.

goal _ (i,j : index) :
  happens(A(i)) =>
f(i)@A(i) = fun (x : message) => (<x, input@A(i)>,j).
Proof. 
  rewrite /f /=. 
  checkfail auto exn GoalNotClosed. 
Abort.

(*------------------------------------------------------------------*)
goal _ (i : index, z : message) :
  happens(A(i)) =>
  (f(i)@A(i)) z = (<z, input@A(i)>,i).
Proof.
  rewrite /f /=. 
  auto. 
Qed.
