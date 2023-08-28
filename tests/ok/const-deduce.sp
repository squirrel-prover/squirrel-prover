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

(* succeeds, `i` computable by the adversary *)
global goal _ (i:T[adv]) :
  equiv(seq(j:T => n j)) -> equiv (n i).
Proof.
  intro H.
  apply H.
Qed.

(*------------------------------------------------------------------*)
type F[finite, fixed].

name m : F -> message.

(* succeeds, `i` constant over a fixed+finite hence computable *)
global goal _ (i:F[const]) :
  equiv(seq(j:F => m j)) -> equiv (m i).
Proof.
  intro H.
  apply H.
Qed.
