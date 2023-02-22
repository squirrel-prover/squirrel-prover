system null.

type T[finite]

name n : T -> message.

(* fails because `i` is unknown to the adversary *)
global goal _ (i:T) :
 equiv(seq(j:T => n(j))) -> equiv (n(i)).
Proof.
  intro H.
  checkfail apply H exn ApplyMatchFailure.
Abort.

(* succeeds, `i` constant hence computable *)
global goal _ (i:T[const]) :
  equiv(seq(j:T => n(j))) -> equiv (n(i)).
Proof.
  intro H.
  apply H.
Qed.
