include Core.

namespace Real.
  type real.
  
  op ( + ) : real -> real -> real.
  op opp : real -> real.
  op ( - ) (x : real) (y : real) = x + (opp y).

  abstract ( * ) : real -> real -> real.
  op inv : real -> real.
  op div (x : real) (y : real) = x * (inv y).

  abstract leq : real -> real -> bool
  abstract z_r : real 
  abstract o_r : real 
  abstract t_r : real 
   
  axiom [any] add_assoc : assoc ( + ).
  axiom [any] mul_assoc : assoc ( * ).
end Real.
