(*
  Squirrel prelude file.
  Can only be used to declare objects in the symbol table.
*)


op (= ) ['a] : 'a -> 'a -> bool.
op (<>) ['a] : 'a -> 'a -> bool. 
op (<=) ['a] : 'a -> 'a -> bool. 
op (< ) ['a] : 'a -> 'a -> bool. 
op (>=) ['a] : 'a -> 'a -> bool. 
op ( > ) ['a] (x : 'a) (y : 'a) = y < x.

op witness ['a] : 'a.

op zeroes : message -> message.

system Empty = null.

(*------------------------------------------------------------------*)
type quantum_message.

type quantum_measures_rnd[serializable, finite].

type string[serializable, fixed].
  
type int[well_founded, fixed, serializable].

namespace Real.
type t.
op of_int : int -> t.
op z = of_int 0.
end Real.
(*------------------------------------------------------------------*)
(* `Classic` defines the macros for the classical execution model *)
open Classic.
