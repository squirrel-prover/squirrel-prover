(* takes operators declarations in `operators.sp`, and erase all types
  to test automatic type inference. *)

op triple (x, y, z : _) : _ = <x, <y, z>>.

(* implicit return type *)
op triple' (x, y, z : _) = <x, <y, z>>.

(* generic pairs *)
abstract gpair ['a] : 'a -> 'a -> 'a.

op gtriple  ['a] (x, y, z : _ ) : 'a = gpair x (gpair y z).
op gtriple1 ['a] (x, y, z : 'a) :  _ = gpair x (gpair y z). 

op foo  ['a] (x : _ ) : 'a = gtriple x x x.
op foo1 ['a] (x : 'a) : _  = gtriple x x x.

system null.

op (~<) (x,y : _) : _ = if x = y && x = empty then zero.

op misc1 ['a] ((x,y) : 'a * _ ) = if x = y then x else x.
op misc2 ['a] ((x,y) : _  * 'a) = if x = y then x else x.
