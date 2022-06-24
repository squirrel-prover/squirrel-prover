name n : message
name k : message
hash h
abstract f : message -> message
system null.

goal [default] _ :
  h(n,k) = <f(n),h(f(n),k)> => f(n) = n.
Proof.
  intro Heq.
  euf Heq. 
  auto.
Qed.


(* goal [any] _ : *)
(*   h(n,k) = <f(n),h(f(n),k)> => f(n) = n. *)
(* Proof. *)
(*   intro Heq. *)
(*   euf Heq.  *)
(*   auto. *)
(* Qed. *)
