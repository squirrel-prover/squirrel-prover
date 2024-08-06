include Core.

namespace Int. 
  op ( + ) : int -> int -> int.
  op opp : int -> int.
  op ( - ) (x : int) (y : int) = x + (opp y).

  abstract ( * ) : int -> int -> int.
   
  axiom [any] add_assoc : assoc ( + ).
  axiom [any] mul_assoc : assoc ( * ).
end Int.
