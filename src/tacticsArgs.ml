module L = Location

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
type naming_pat =
  | Unnamed                  (** '_' *)
  | AnyName                  (** '?' *)
  | Named   of string

type and_or_pat =
  | Or      of simpl_pat list
  (** e.g. \[H1 | H2\] to do a case on a disjunction. *)
        
  | Split 
  (** e.g. \[\] to do a case. *)

  | And     of simpl_pat list
  (** e.g. \[H1 H2\] to destruct a conjunction. *)
        
and simpl_pat =
  | SAndOr of and_or_pat
  | SNamed of naming_pat

type intro_pattern =
  | Star     of Location.t    (** '*' *)
  | Simpl of simpl_pat

(*------------------------------------------------------------------*)
let pp_naming_pat fmt = function
  | Unnamed -> Fmt.pf fmt "_"
  | AnyName -> Fmt.pf fmt "?"
  | Named s -> Fmt.pf fmt "%s" s

let rec pp_and_or_pat fmt = function
  | Or      l ->
    let sep fmt () = Fmt.pf fmt "|" in
    Fmt.pf fmt "[%a]" (Fmt.list ~sep pp_simpl_pat) l

  | And      l ->
    let sep fmt () = Fmt.pf fmt " " in
    Fmt.pf fmt "[%a]" (Fmt.list ~sep pp_simpl_pat) l

  | Split -> Fmt.pf fmt "[]"

and pp_simpl_pat fmt = function
  | SAndOr ao_ip -> pp_and_or_pat fmt ao_ip
  | SNamed n_ip  -> pp_naming_pat fmt n_ip

let rec pp_intro_pat fmt = function
  | Star     _    -> Fmt.pf fmt "*"
  | Simpl s_ip -> pp_simpl_pat fmt s_ip

let pp_intro_pats fmt args =
  let pp_sep fmt () = Fmt.pf fmt "@ " in
  Fmt.pf fmt "@[<hv 2>%a@]"
    (Fmt.list ~sep:pp_sep pp_intro_pat) args

(*------------------------------------------------------------------*)
(** handler for intro pattern application *)
type ip_handler = [
  | `Var of Vars.evar (* Careful, the variable is not added to the env  *)
  | `Hyp of Ident.t
]
  
(*------------------------------------------------------------------*)
(** Parsed arguments for rewrite *)
type rw_arg = { 
  rw_mult : [`Once | `Many | `Any ];         (* ε | ! | ? *)
  rw_dir  : [`LeftToRight | `RightToLeft ] L.located;
  rw_type : [`Form of Theory.formula | `Expand of Theory.lsymb];
}


(*------------------------------------------------------------------*)
(** One tactic argument (in the parser) *)
type parser_arg =
  | String_name of lsymb
  | Int_parsed  of int
  | Theory      of Theory.term
  | IntroPat    of intro_pattern list
  | AndOrPat    of and_or_pat
  | SimplPat    of simpl_pat
  | RewriteIn   of lsymb option * rw_arg list
      
type ('a, 'b) pair

(*------------------------------------------------------------------*)
(* The types are explicit, in order to type the tactics. *)
type _ sort =
  | None      : unit sort

  | Message   : Sorts.message   sort
  | Boolean   : Sorts.boolean   sort
  | Timestamp : Sorts.timestamp sort        
  | Index     : Sorts.index     sort

  | ETerm     : Theory.eterm    sort
  (** Boolean, timestamp or message *)
        
  | Int       : int sort
  | String    : lsymb sort
  | Pair      : ('a sort * 'b sort) -> ('a * 'b) sort
  | Opt       : 'a sort -> ('a option) sort

(*------------------------------------------------------------------*)
type _ arg =
  | None      : unit arg 

  | Message   : Term.message   -> Sorts.message   arg
  | Boolean   : Term.formula   -> Sorts.boolean   arg
  | Timestamp : Term.timestamp -> Sorts.timestamp arg
  | Index     : Vars.index     -> Sorts.index     arg

  | ETerm     : 'a Sorts.sort * 'a Term.term * Location.t -> Theory.eterm arg

  | Int       : int -> int arg
  | String    : lsymb -> lsymb arg
  | Pair      : 'a arg * 'b arg -> ('a * 'b) arg
  | Opt       : ('a sort * 'a arg option) -> ('a option) arg

(*------------------------------------------------------------------*)
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
  | ETerm _     -> ETerm

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

(*------------------------------------------------------------------*)
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
      | ETerm    , ETerm     -> t
      | Int      , Int       -> t
      | String   , String    -> t
      | None     , None      -> t
      | _ -> raise Uncastable
    end

(*------------------------------------------------------------------*)
let sort_to_string  : type a. a sort -> string = function
  | None      -> ""
  | Message   -> "m"
  | Boolean   -> "f"
  | Timestamp -> "ts"
  | Index     -> "idx"
  | ETerm     -> "t"
  | Int       -> "i"
  | String    -> "H"
  | Pair _
  | Opt _ -> assert false

(*------------------------------------------------------------------*)
type counters = { message : int;
                  boolean : int;
                  timestamp : int;
                  index : int;
                  int : int;
                  string : int}

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
  | ETerm
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
  | ETerm
  | Int
  | String ->
    begin
      match Ms.find_opt (Sort s) table with
      | Some i when i > 1 -> true
      | _ -> false
    end

  | Opt _ -> assert false
  | Pair _ -> assert false

let rec pp_aux_sort : type a. table -> table ref -> bool -> Format.formatter -> a sort  -> unit =
  fun init_table counter_table printopt ppf s -> match s with
  | None
  | Message
  | Boolean
  | Timestamp
  | Index
  | ETerm
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


(*------------------------------------------------------------------*)
type tac_arg_error_i =
  | CannotConvETerm 

type tac_arg_error = L.t * tac_arg_error_i

exception TacArgError of tac_arg_error

let pp_tac_arg_error_i ppf = function
  | CannotConvETerm -> Fmt.pf ppf "cannot convert the term as a message, \
                                   timestamp, boolean and an index"

let pp_tac_arg_error pp_loc_err ppf (loc,e) =
  Fmt.pf ppf "%a%a"
    pp_loc_err loc
    pp_tac_arg_error_i e

let tac_arg_error loc e = raise (TacArgError (loc,e))
    
(*------------------------------------------------------------------*)

let convert_as_lsymb parser_args = match parser_args with
  | [Theory (L.{ pl_desc = App (p,[]) } )] ->
    Some p
  | _ -> None

let convert_args table env parser_args tactic_type =
  let conv_cntxt = Theory.{ table = table; cntxt = InGoal; } in
  
  let rec conv_args parser_args tactic_type env =
    let tsubst = Theory.subst_of_env env in    
    match parser_args, tactic_type with
    | [Theory p], Sort Timestamp ->
      Arg (Timestamp (Theory.convert conv_cntxt tsubst p Sorts.Timestamp))

    | [Theory p], Sort Message ->
      Arg (Message   (Theory.convert conv_cntxt tsubst p Sorts.Message))

    | [Theory p], Sort Boolean ->
      Arg (Boolean   (Theory.convert conv_cntxt tsubst p Sorts.Boolean))

    | [Theory p], Sort ETerm ->
      let et = match Theory.econvert conv_cntxt tsubst p with
        | Some (Theory.ETerm (s,t,l)) -> ETerm (s,t,l)
        (* FIXME: this does not give any conversion error to the user. *)
        | None -> tac_arg_error (L.loc p) CannotConvETerm in
      Arg et

    | [Theory (L.{ pl_desc = App (p,[]) } )], Sort String ->
      Arg (String p) (* TODO: location *)

    | [Int_parsed i], Sort Int ->
      Arg (Int i)

    | [Theory t], Sort String ->
      raise Theory.(Conv (L.loc t, String_expected (L.unloc t)))

    | [Theory t], Sort Int ->
      raise Theory.(Conv (L.loc t, Int_expected (L.unloc t)))

    | [Theory p], Sort Index ->
      Arg (Index (Theory.convert_index table tsubst p))
    (* old code: *)
    (* Arg (Index (Theory.convert_index table tsubst (Theory.var p))) *)

    | th1::q, Sort (Pair (Opt s1, s2)) ->
      begin match conv_args [th1] (Sort (Opt s1)) env with
        | Arg arg1 ->
          let Arg arg2 = conv_args q (Sort s2) env in
          Arg (Pair (arg1, arg2))
        | exception Theory.(Conv _) ->
          let Arg arg2 = conv_args (th1::q) (Sort s2) env in
          Arg (Pair (Opt (s1, None), arg2))
      end

    | th1::q, Sort (Pair (s1, s2)) ->
      let Arg arg1 = conv_args [th1] (Sort s1) env in
      let Arg arg2 = conv_args q (Sort s2) env in
      Arg (Pair (arg1, arg2))

    | [], Sort (Opt a) ->
      Arg (Opt (a, None))

    | [], Sort (Pair (Opt a, b)) ->
      let Arg arg2 = conv_args [] (Sort b) env in
      Arg (Pair (Opt (a, None), arg2))

    | [th], Sort (Opt a) ->
      let Arg arg = conv_args [th] (Sort a) env in
      Arg (Opt
             (a,
              (Some (cast a arg))
             )
          )

    | [], Sort None -> Arg None
      
    (* TODO: location *)
    | [], _ -> raise Theory.(Conv (L._dummy, Tactic_type "more arguments expected"))

    (* TODO: location *)
    | p, _  ->
      raise Theory.(Conv (L._dummy,
                          Tactic_type "tactic argument error \
                                       (maybe you gave too many arguments?)"))

  in
  conv_args parser_args tactic_type env
