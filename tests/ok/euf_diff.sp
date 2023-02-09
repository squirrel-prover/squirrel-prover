name n : message
name k : message
hash h
abstract f : message -> message
abstract g : message -> message
system null.

goal [default] _ :
  h(n,k) = diff(<f(n),h(f(n),k)>,empty) => f(n) = n.
Proof.
  intro Heq.
  euf Heq. 
  auto.
Qed.

goal [default] _ :
  h(n,k) = diff(<f(n),h(f(n),k)>,h(g(n),k)) => f(n) = n || g(n) = n.
Proof.
  intro Heq.
  euf Heq. 
  auto.
  auto.
Qed.
