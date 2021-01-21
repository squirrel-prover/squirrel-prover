(** Arguments types for tactics, used to unify the declaration of tactics
   requiring type conversions.contents. *)

(* Types defined directly in the parsing. Note that all tactics not defined in
   the parser must rely on the Theory type, even to parse strings. *)
type parser_arg =
  | String_name of string
  | Int_parsed  of int
  | Theory      of Theory.term

(* The types are explicit, in order to type the tactics. *)
type _ sort =
  | None      : unit sort
  | Message   : Sorts.message sort
  | Boolean   : Sorts.boolean sort
  | Timestamp : Sorts.timestamp sort
  | Index     : Sorts.index sort
  | Int       : int sort
  | String    : string sort
  | Pair      : ('a sort * 'b sort) -> ('a * 'b) sort
  | Opt       : 'a sort -> ('a option) sort

type _ arg =
  | None      : unit arg
  | Message   : Term.message -> Sorts.message arg
  | Boolean   : Term.formula -> Sorts.boolean arg
  | Timestamp : Term.timestamp -> Sorts.timestamp arg
  | Index     : Vars.index -> Sorts.index arg
  | Int       : int -> int arg
  | String    : string -> string arg
  | Pair      : 'a arg * 'b arg -> ('a * 'b) arg
  | Opt       : ('a sort * 'a arg option) -> ('a option) arg


val sort : 'a arg -> 'a sort

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

exception Uncastable

val cast:  'a sort -> 'b arg -> 'a arg

val pp_esort : Format.formatter -> esort -> unit
