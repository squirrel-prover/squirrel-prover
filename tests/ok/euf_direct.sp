set autoIntro=false.

name n : message
name k : message
hash h
abstract f : message->message
system null.

goal test :
  h(n,k) = <f(n),h(f(n),k)> => f(n) = n.
Proof.
  intro Heq.
  euf Heq. 
  auto.
Qed.
