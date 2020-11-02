(** Arguments types for tactics, used to unify the declaration of tactics
   requiring type conversions.contents. *)

(* Types defined directly in the parsing. Note that all tactics not defined in
   the parser must rely on the Theory type, even to parse strings. *)
type parser_arg =
  | String_name of string
  | Int of int
  | Theory of Theory.term

(* The types are explicit, in order to type the tactics. *)
type _ sort =
  | Message : Sorts.message sort
  | Boolean : Sorts.boolean sort
  | Timestamp : Sorts.timestamp sort
  | Index : Sorts.index sort
  | AInt : int sort
  | String : string sort

type _ arg =
  | Message : Term.message -> Sorts.message arg
  | Boolean : Term.formula -> Sorts.boolean arg
  | Timestamp : Term.timestamp -> Sorts.timestamp arg
  | Index : Vars.index -> Sorts.index arg
  | AInt : int -> int arg
  | String : string -> string arg

val sort : 'a arg -> 'a sort

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

exception Uncastable

val cast:  'a sort -> 'b arg -> 'a arg
