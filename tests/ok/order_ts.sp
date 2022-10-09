include Basic.

(* Careful, our order on timestamp is **NOT** reflexive! *)
goal [any] _ (t : timestamp) : t <= t.
Proof. checkfail auto exn GoalNotClosed. Abort.

goal [any] _ (t : timestamp) : not (t < t).
Proof. auto. Qed.
