(*
  Squirrel prelude file.
  Can only be used to declare objects in the symbol table.
*)

abstract (= ) ['a] : 'a -> 'a -> bool.
abstract (<>) ['a] : 'a -> 'a -> bool. 
abstract (<=) ['a] : 'a -> 'a -> bool. 
abstract (< ) ['a] : 'a -> 'a -> bool. 
abstract (>=) ['a] : 'a -> 'a -> bool. 
abstract (> ) ['a] : 'a -> 'a -> bool. 

abstract witness ['a] : 'a.

abstract zeroes : message -> message.

system Empty = null.

(*------------------------------------------------------------------*)
type quantum_message.

(*------------------------------------------------------------------*)
(* `Classic` defines the macros for the classical execution model *)
open Classic.
