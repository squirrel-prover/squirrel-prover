mutable s : message = empty

abstract v : message

channel c

system
  !_i
  in(c,x);
  s := <s,x>;
  out(c,s).

lemma _ (a:index): happens(A(a)) => s@A(a) = <s@pred(A(a)),input@A(a)>.
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
(* check that mutable types are inferred *)
mutable s2 = empty.

abstract i0 : index.

mutable s3 x y z = (x = y && x = i0 && z = i0).
