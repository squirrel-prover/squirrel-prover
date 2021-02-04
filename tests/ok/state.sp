set autoIntro=false.

mutable s : message
abstract v : message

channel c

system
  !_i
  in(c,x);
  s := <s,x>;
  out(c,s).

goal forall (a:index), s@A(a) = <s@pred(A(a)),input@A(a)>.
Proof.
 by auto.
Qed.
