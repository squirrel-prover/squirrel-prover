name n : index->message

channel c

system !_i out(c,n(i)).

goal _ (j:index,t:timestamp) : n(j) = input@t => A(j) < t.
Proof.
  nosimpl(intro Heq).
  nosimpl(fresh Heq).
  nosimpl(intro H).
  constraints.
Qed.

(* we check that this implies that A(j) happened. *)
goal _ (j:index,t:timestamp) : n(j) = input@t => happens(A(j)).
Proof.
  intro Heq.
  fresh Heq.
  auto.
Qed.
