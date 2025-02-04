include Logic.
include Int.
include FiniteTypes.

namespace Real.

  op ( + ) : t -> t -> t.
  op opp : t -> t.
  op ( - ) (x : t) (y : t) = x + (opp y).

  abstract ( * ) : t -> t -> t.
  op inv : t -> t.
  op div (x : t) (y : t) = x * (inv y).


  exact axiom [any] add_assoc     : assoc           ( + ).
  exact axiom [any] add_comm      : commutative     ( + ).
  exact axiom [any] add_neutral_l : left_neutral  z ( + ).
  exact lemma [any] add_neutral_r : right_neutral z ( + ).
  Proof. rewrite /right_neutral add_comm. apply add_neutral_l. Qed.

  exact axiom [any] mul_assoc     : assoc                    ( * ).
  exact axiom [any] mul_comm      : commutative              ( * ).
  exact axiom [any] mul_neutral_l : left_neutral (of_int 1)  ( * ).
  exact lemma [any] mul_neutral_r : right_neutral (of_int 1) ( * ).
  Proof. rewrite /right_neutral mul_comm. apply mul_neutral_l. Qed.

  exact axiom [any] mul_absorb_l  : left_absorbing  z ( * ).
  exact lemma [any] mul_absorb_r  : right_absorbing z ( * ).
  Proof. rewrite /right_absorbing mul_comm. apply mul_absorb_l. Qed.


  (*------------------------------------------------------------------*)
  exact axiom [any] mul_distrib_plus x y z : (x + y) * z = x*z + y *z.
  exact axiom [any] mul_distrib_minus x y z : (x - y) * z = x*z - y *z.
  exact axiom [any] minus_opp x : x - x = z.
  exact axiom [any] div_inv x : x <> z => div x  x = of_int 1.

  (*------------------------------------------------------------------*)
  exact axiom [any] add_of_int x y : of_int( Int.(+)   x y ) = of_int x + of_int y.
  exact axiom [any] minus_of_int x y : of_int( Int.(-)   x y ) = of_int x - of_int y.
  exact axiom [any] mul_of_int x y : of_int( Int.( * ) x y ) = of_int x * of_int y.

  (*------------------------------------------------------------------*)

  (* Sum over a finite type `'a` 
     (and an arbitrary value over other types). *) 
  op sum ['a] (p : 'a -> bool) (v : 'a -> t) : t.

  exact axiom [any] sum_const ['a] (p : 'a -> bool) (c : t) : 
    sum p (fun _ => c) = of_int FiniteTypes.card['a] * c.

  exact lemma [any] sum_zero ['a] (p : 'a -> bool) : sum p (fun _ => z) = z.
  Proof.
    by rewrite sum_const mul_absorb_r.
  Qed.  
end Real.
