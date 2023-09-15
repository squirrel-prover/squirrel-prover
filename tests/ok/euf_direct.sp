name n : message
name k : message
hash h
abstract f : message -> message
system null.

lemma [default] _ :
  h(n,k) = <f(n),h(f(n),k)> => f(n) = n.
Proof.
  intro Heq.
  euf Heq. 
  auto.
Qed.

(*------------------------------------------------------------------*)
name n1 : index -> message.
abstract p : index -> bool.

abstract a : message.

lemma [default] _ :
  h(a,k) = try find i such that p i in <f(n1 i),h(f(n1 i),k)> else h(f n, k) =>
  (exists (i : index), a = f (n1 i)) ||
  (a = f n && forall (i : index), not (p i)).
Proof.
  intro Heq.
  euf Heq. 
  + by intro [i H]; left; exists i. 
  + intro ?; right; auto.
Qed.

