mutable s : message = empty
abstract v : message

channel c

system
  !_i
  in(c,x);
  s := <s,x>;
  out(c,s).

goal _ (a:index):   happens(A(a)) => s@A(a) = <s@pred(A(a)),input@A(a)>.
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
(* check that mutable types are inferred *)
mutable s2 = empty.
