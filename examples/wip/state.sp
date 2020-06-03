mutable s : message
mutable permut : message
abstract v : message

channel c

system
  !_i
  in(c,x);
  s := <s,x>;
  s := s;
  out(c,s).

goal forall (a:index), s@A(a) = <s@pred(A(a)),input@A(a)>.
Proof.
Qed.
