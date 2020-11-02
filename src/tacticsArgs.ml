

type parser_arg =
  | String_name of string
  | Int of int
  | Theory of Theory.term

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

let rec sort : type a. a arg -> a sort =
  function
  | Message _ -> Message
  | Boolean _ -> Boolean
  | Timestamp _ ->  Timestamp
  | Index _ -> Index
  | AInt _ -> AInt
  | String _ -> String

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

exception Uncastable

let cast: type a b. a sort -> b arg -> a arg =
  fun kind t ->
  match kind, sort t with
  | Message, Message -> t
  | Boolean, Boolean -> t
  | Timestamp, Timestamp -> t
  | Index, Index -> t
  | AInt, AInt -> t
  | String, String -> t
  | _ -> raise Uncastable
