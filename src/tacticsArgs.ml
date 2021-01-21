

type parser_arg =
  | String_name of string
  | Int_parsed  of int
  | Theory      of Theory.term

type ('a, 'b) pair

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

let rec sort : type a. a arg -> a sort =
  function
  | None        -> None
  | Message _   -> Message
  | Boolean _   -> Boolean
  | Timestamp _ -> Timestamp
  | Index _     -> Index
  | Int _       -> Int
  | String _    -> String
  | Pair (a, b) -> Pair (sort a, sort b)
  | Opt (s,_)   -> Opt s

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
      | Message  , Message   -> t
      | Boolean  , Boolean   -> t
      | Timestamp, Timestamp -> t
      | Index    , Index     -> t
      | Int      , Int       -> t
      | String   , String    -> t
      | None     , None      -> t
      | _ -> raise Uncastable
    end

let sort_to_string  : type a. a sort -> string = function
  | None      -> ""
  | Message   -> "m"
  | Boolean   -> "f"
  | Timestamp -> "ts"
  | Index     -> "idx"
  | Int       -> "i"
  | String    -> "H"
  | _ -> assert false

type counters = { message : int; boolean : int; timestamp : int; index : int; int : int; string : int}

module Ms = Map.Make (struct type t = esort let compare = Stdlib.compare end)


type table = int Ms.t

let empty_table = Ms.empty

(* To pretty print, we first count all occurences of each sort. If a sort index
   occurs only once, it will be pp with idx. If it occurs multiple times, idx1,
   idx2,... will be used. *)
let rec setup_counters : type a. table -> a sort -> table =
  fun table s -> match s with
  | None
  | Message
  | Boolean
  | Timestamp
  | Index
  | Int
  | String ->
    begin
      match Ms.find_opt (Sort s) table with
      | None -> Ms.add (Sort s) 1 table
      | Some i -> Ms.add (Sort s) (i+1) table
    end
  | Opt a -> setup_counters table a
  | Pair (a, b) -> setup_counters (setup_counters table a) b

(* on a table set up with setupcounters, specify if the given sort occur more
   than once. *)
let has_multiple_occurences  : type a. table -> a sort -> bool =
  fun table s -> match s with
  | None
  | Message
  | Boolean
  | Timestamp
  | Index
  | Int
  | String ->
    begin
      match Ms.find_opt (Sort s) table with
      | Some i when i > 1 -> true
      | _ -> false
    end
  | _ -> assert false

let rec pp_aux_sort : type a. table -> table ref -> bool -> Format.formatter -> a sort  -> unit =
  fun init_table counter_table printopt ppf s -> match s with
  | None
  | Message
  | Boolean
  | Timestamp
  | Index
  | Int
  | String ->
    if has_multiple_occurences init_table s then
      let i =
        begin
          match Ms.find_opt (Sort s) !counter_table with
          | None -> counter_table := Ms.add (Sort s) 1 !counter_table; 1
          | Some i -> counter_table := Ms.add (Sort s) (i+1) !counter_table; i+1
        end
      in
      Fmt.pf ppf (if printopt then "[%s%i]" else  "%s%i") (sort_to_string s) i
    else
      Fmt.pf ppf (if printopt then "[%s]" else  "%s") (sort_to_string s)

  | Opt a -> pp_aux_sort init_table counter_table true ppf a
  | Pair (a, b) -> Fmt.pf ppf "%a %a"
                     (pp_aux_sort init_table counter_table printopt) a
                     (pp_aux_sort init_table counter_table printopt) b

let pp_esort ppf (Sort s) =
  let init_table = setup_counters (empty_table) s in
  let counter_table = ref empty_table in
  Fmt.pf ppf "%a" (pp_aux_sort init_table counter_table false) s
