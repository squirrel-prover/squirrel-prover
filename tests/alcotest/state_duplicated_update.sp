abstract n0 : message
abstract v : message

mutable s : message = n0

channel c

system
  !_i
  in(c,x);
  s := <s,x>;
  s := s;
  out(c,s).

goal _ (a:index) : s@A(a) = <s@pred(A(a)),input@A(a)>.
Proof.
Qed.
