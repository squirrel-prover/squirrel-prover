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

type string[fixed].
  
type int[well_founded, fixed].

(*------------------------------------------------------------------*)
(* `Classic` defines the macros for the classical execution model *)
open Classic.
