include Core.

namespace Int. 
  op ( + ) : int -> int -> int.
  op opp : int -> int.
  op ( - ) (x : int) (y : int) = x + (opp y).

  abstract ( * ) : int -> int -> int.
   
  exact axiom [any] add_assoc     : assoc           ( + ).
  exact axiom [any] add_comm      : commutative     ( + ).
  exact axiom [any] add_neutral_l : left_neutral  0 ( + ).
  exact lemma [any] add_neutral_r : right_neutral 0 ( + ).
  Proof. rewrite /right_neutral add_comm. apply add_neutral_l. Qed.

  (*------------------------------------------------------------------*)
  exact axiom [any] mul_assoc     : assoc           ( * ).
  exact axiom [any] mul_comm      : commutative     ( * ).
  exact axiom [any] mul_neutral_l : left_neutral  1 ( * ).
  exact lemma [any] mul_neutral_r : right_neutral 1 ( * ).
  Proof. rewrite /right_neutral mul_comm. apply mul_neutral_l. Qed.
  exact axiom [any] mul_absorb_l  : left_absorbing   0 ( * ).
  exact lemma [any] mul_absorb_r  : right_absorbing  0 ( * ).
  Proof. rewrite /right_absorbing mul_comm. apply mul_absorb_l. Qed.

  exact axiom [any] minus_opp x : x - x = 0.
end Int.
