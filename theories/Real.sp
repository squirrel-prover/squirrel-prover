(* TODO:Concrete : Add non bit-string encodable flag*)
type real.

abstract addr : real -> real -> real
abstract minus : real -> real
abstract leq : real -> real -> bool
abstract z_r : real


op assoc ['a]  (f : 'a -> 'a ->  'a) = forall x y z, f (f x y) z = f x (f y z).

axiom [any] add_assoc : assoc addr.
