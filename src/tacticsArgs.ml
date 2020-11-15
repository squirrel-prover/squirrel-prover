

type parser_arg =
  | String_name of string
  | Int_parsed of int
  | Theory of Theory.term

type ('a, 'b) pair

type _ sort =
  | Message : Sorts.message sort
  | Boolean : Sorts.boolean sort
  | Timestamp : Sorts.timestamp sort
  | Index : Sorts.index sort
  | Int : int sort
  | String : string sort
  | Pair : ('a sort * 'b sort) -> ('a * 'b) sort
  | Opt : 'a sort -> ('a option) sort

type _ arg =
  | Message : Term.message -> Sorts.message arg
  | Boolean : Term.formula -> Sorts.boolean arg
  | Timestamp : Term.timestamp -> Sorts.timestamp arg
  | Index : Vars.index -> Sorts.index arg
  | Int : int -> int arg
  | String : string -> string arg
  | Pair : 'a arg * 'b arg -> ('a * 'b) arg
  | Opt : ('a sort * 'a arg option) -> ('a option) arg

let rec sort : type a. a arg -> a sort =
  function
  | Message _ -> Message
  | Boolean _ -> Boolean
  | Timestamp _ ->  Timestamp
  | Index _ -> Index
  | Int _ -> Int
  | String _ -> String
  | Pair (a, b) -> Pair (sort a, sort b)
  | Opt (s,_) -> Opt s

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

exception Uncastable

let rec cast: type a b. a sort -> b arg -> a arg =
  fun kind t ->
  match kind, t with
  | Pair (a,b), Pair (c,d) -> Pair (cast a c, cast b d)
  | Opt s, Opt (r, None) -> Opt(s,None)
  | Opt s, Opt (r, Some q) -> Opt(s, Some (cast s q))
  | _ -> begin
      match kind, sort t with
      | Message, Message -> t
      | Boolean, Boolean -> t
      | Timestamp, Timestamp -> t
      | Index, Index -> t
      | Int, Int -> t
      | String, String -> t
      | _ -> raise Uncastable
    end
