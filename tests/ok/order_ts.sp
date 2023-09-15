include Basic.

(* Careful, our order on timestamp is **NOT** reflexive! *)
lemma [any] _ (t : timestamp) : t <= t.
Proof. checkfail auto exn GoalNotClosed. Abort.

lemma [any] _ (t : timestamp) : not (t < t).
Proof. auto. Qed.
