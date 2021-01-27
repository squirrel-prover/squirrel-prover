system null.

(* This should not pass: it is not true for the initial timestamp epsilon,
 * though it is true for all actions. *)

goal forall (t:timestamp), t <= pred(t) => False.
Proof.
  intro t Hleq.
Qed.
