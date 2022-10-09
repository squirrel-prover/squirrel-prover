(* test the interaction of rewriting and systems:
   conditions under which the rewriting can occur must be correctly 
   projected. *)

system [a] null.
system [b] null.

abstract c : message.
abstract d : message.

axiom [a] ax (tau:timestamp) : diff(tau = init,False) => input@tau = diff(c,d).

axiom [any] refl (x:message) : x = x.

goal [a/left] _ (tau:timestamp) : tau = init => input@tau = c.
Proof.
  intro H.
  rewrite ax.
  assumption.
  apply refl.
Qed.
