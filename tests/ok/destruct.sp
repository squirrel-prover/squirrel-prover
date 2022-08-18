system null.

axiom exists_idx : exists i:index, True.

goal _ : False.
Proof.
  use exists_idx.
  destruct H as [i HH].
  admit.
Qed.

goal _ (x,y,a,b : message) : <x,y> = <a,b> => x = a && y = b.
Proof.
  intro [H1 H2]. 
  split; assumption.
Qed.

(*------------------------------------------------------------------*)
goal _ (x, y : boolean) : (x <=> y) => x => y.
Proof. 
  intro [H1 H2].
  assumption H1.
Qed.

goal _ (x, y : boolean) : (x <=> y) => y => x.
Proof. 
  intro [H1 H2].
  assumption H2.
Qed.

(*------------------------------------------------------------------*)
goal _ (x, y : boolean) : (x <=> y) => y => x.
Proof.
  intro [H1 H2].
  assumption H2.
Qed.

(* global goal _ (x, y : boolean) : [x <=> y] -> [x => y]. *)
(* Proof. *)
(*   intro [H1 H2]. *)
(*   assumption H1. *)
(* Qed. *)
