system null.

(* This should pass. *)

goal two :
  not(False).
Proof.
Qed.

goal False => False.
Proof.
  (* Intro does not handle this formula,
   * and add_fact does not handle False.
   * For a more interesting (?) variant: happens(A)=>False
   * where the condition of A is just False. *)
Qed.
