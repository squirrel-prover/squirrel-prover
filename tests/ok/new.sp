(* test type inferrence in processes *)

type T1.
type T2.

abstract f : T1 -> T2 -> message.

channel c.

process foo =
  new x : _;
  new y : _;
  out(c,f x y).

system
  new x : _;
  new y : _;
  out(c,f x y).

