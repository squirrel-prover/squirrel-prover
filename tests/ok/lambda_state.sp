mutable f: message -> message = fun (x : message) => x.

channel c.

process A(i : index) =
  in(c,m);
  f := fun (x : message) => <x,m>;
  out(c,empty).

system !_i A(i).

goal _ (i : index) :
  happens(A(i)) =>
  f@A(i) = fun (x : message) => <x, input@A(i)>.
Proof. auto. Qed.

goal _ (i,j : index) :
  happens(A(i)) =>
  f@A(i) = fun (x : message) => <x, input@A(j)>.
Proof. checkfail auto exn GoalNotClosed. Abort.

(*------------------------------------------------------------------*)
goal _ (i : index, z : message) :
  happens(A(i)) =>
  (f@A(i)) z = <z, input@A(i)>.
Proof. auto. Qed.
