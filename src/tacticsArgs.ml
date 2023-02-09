module L = Location

module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** Tactic target. *)
type in_target = [
  | `Goal
  | `All
  | `Hyps of lsymb list         (* hypotheses, or frame elements *)
]

let pp_in_target ppf (in_t : in_target) =
  match in_t with
  | `Goal      -> ()
  | `All -> Fmt.pf ppf " in *"
  | `Hyps symb ->
    Fmt.pf ppf " in %a"
      (Fmt.list ~sep:Fmt.comma Fmt.string) (L.unlocs symb)

(*------------------------------------------------------------------*)
(** {2 Tactics named args} *)

type named_arg =
  | NArg of lsymb               (** '~id' *)

type named_args = named_arg list

(*------------------------------------------------------------------*)
(** {2 Simplification item} *)
    
type s_item_body =
  | Tryauto      of Location.t    (** '//' *)
  | Tryautosimpl of Location.t    (** '//' *)
  | Simplify     of Location.t    (** '//=' *)

type s_item = s_item_body * named_args
              
let pp_s_item_body fmt = function
  | Simplify      _ -> Fmt.pf fmt "/="
  | Tryauto       _ -> Fmt.pf fmt "//"
  | Tryautosimpl  _ -> Fmt.pf fmt "//="

let pp_s_item fmt (s, named_args) =
  if named_args = [] then pp_s_item_body fmt s
  else
    Fmt.pf fmt "[%a ...]" pp_s_item_body s

(*------------------------------------------------------------------*)
(** {2 Parsed arguments for rewrite} *)

type rw_count = 
    | Once                   (** ε *)
    | Many                   (** ! *)
    | Any                    (** ? *)
    | Exact of int           (** i! where [i] is an integer *)

type rw_dir = [`LeftToRight | `RightToLeft ] L.located

(** General rewrite item *)
type 'a rw_item_g = {
  rw_mult : rw_count;
  rw_dir  : rw_dir;
  rw_type : 'a;
}

(** Rewrite or expand item *)
type rw_item = [
  | `Rw        of Theory.p_pt
  | `Expand    of lsymb
  | `ExpandAll of Location.t
] rw_item_g

(** Expand item *)
type expnd_item = [
  | `Expand    of lsymb
  | `ExpandAll of Location.t
] rw_item_g

(** Rewrite equiv item *)
type rw_equiv_item = [
  | `Rw of Theory.p_pt
] rw_item_g

(** Rewrite argument, which is a rewrite or simplification item*)
type rw_arg =
  | R_item   of rw_item
  | R_s_item of s_item

let pp_rw_count ppf = function
  | Once    -> ()
  | Many    -> Fmt.pf ppf "!"
  | Any     -> Fmt.pf ppf  "?"
  | Exact n -> Fmt.pf ppf  "%d" n


let pp_rw_dir ppf d = match L.unloc d with
  | `LeftToRight -> ()
  | `RightToLeft -> Fmt.pf ppf "-"

let pp_rw_type ppf = function
  | `Form f      -> Theory.pp ppf f
  | `Expand s    -> Fmt.pf ppf "/%s" (L.unloc s)
  | `ExpandAll _ -> Fmt.pf ppf "/*"

let pp_rw_item ppf rw_item =
    Fmt.pf ppf "%a%a%a"
      pp_rw_dir   rw_item.rw_dir
      pp_rw_count rw_item.rw_mult
      pp_rw_type  rw_item.rw_type

let pp_rw_arg ppf rw_arg = match rw_arg with
  | R_s_item s -> pp_s_item ppf s
  | R_item _ -> Fmt.pf ppf "..."

(*------------------------------------------------------------------*)
(** Function application argument *)
type fa_arg = rw_count * Theory.term

(*------------------------------------------------------------------*)
type apply_in = lsymb option

let pp_apply_in ppf = function
  | None      -> ()
  | Some symb ->
    Fmt.pf ppf " in %a" Fmt.string (L.unloc symb)

(*------------------------------------------------------------------*)
(** {2 Intro patterns} *)

type naming_pat =
  | Unnamed                  (** '_' *)
  | AnyName                  (** '?' *)
  | Named   of string
  | Approx  of string        (* only used internally *)

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
  | Srewrite of rw_dir      (** -> or <-*)

type intro_pattern =
  | Star   of Location.t    (** '*' *)
  | StarV  of Location.t    (** '>' *)
  | SItem  of s_item
  | SExpnd of expnd_item    (** @/macro *)
  | Simpl  of simpl_pat

(*------------------------------------------------------------------*)
let pp_naming_pat fmt = function
  | Unnamed  -> Fmt.pf fmt "_"
  | AnyName  -> Fmt.pf fmt "?"
  | Named s  -> Fmt.pf fmt "%s" s
  | Approx s -> Fmt.pf fmt "≈%s" s

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

  | Srewrite L.{ pl_desc = `LeftToRight } -> Fmt.pf fmt "->"
  | Srewrite L.{ pl_desc = `RightToLeft } -> Fmt.pf fmt "<-"


let pp_intro_pat fmt = function
  | SItem s    -> pp_s_item fmt s
  | Star     _ -> Fmt.pf fmt "*"
  | StarV    _ -> Fmt.pf fmt ">"
  | Simpl s_ip -> pp_simpl_pat fmt s_ip
  | SExpnd e   -> pp_rw_item fmt e

let pp_intro_pats fmt args =
  let pp_sep fmt () = Fmt.pf fmt "@ " in
  Fmt.pf fmt "@[<hv 2>%a@]"
    (Fmt.list ~sep:pp_sep pp_intro_pat) args

(*------------------------------------------------------------------*)
(** handler for intro pattern application *)
type ip_handler = [
  | `Var of Vars.tagged_var (* Careful, the variable is not added to the env  *)
  | `Hyp of Ident.t
]

(*------------------------------------------------------------------*)
(** {2 Fresh tactic arguments} *)

type fresh_arg =
  | FreshInt of int L.located
  | FreshHyp of lsymb

(*------------------------------------------------------------------*)
(** {2 Trans tactic arguments} *)

type trans_arg =
  | TransSystem of SE.Parse.sys
  | TransTerms  of (int L.located * Theory.term) list

(*------------------------------------------------------------------*)
(** {2 Tactics args} *)

(** A parser tactic argument *)
type parser_arg =
  | String_name  of lsymb
  | Int_parsed   of int L.located
  | Theory       of Theory.term

  | NamingPat    of naming_pat
  | IntroPat     of intro_pattern list
  | AndOrPat     of and_or_pat
  | SimplPat     of simpl_pat

  | Fresh        of named_args * fresh_arg
  | RewriteIn    of rw_arg list * in_target
  | RewriteEquiv of rw_equiv_item
  | Trans        of trans_arg
  | ApplyIn      of named_args * Theory.p_pt * apply_in
  | Have         of simpl_pat option * Theory.any_term
  | HavePt       of Theory.p_pt * simpl_pat option * [`IntroImpl | `None]
  | SplitSeq     of int L.located * Theory.term * Theory.term option
  | ConstSeq     of int L.located * (Theory.term * Theory.term) list
  | MemSeq       of int L.located * int L.located
  | Remember     of Theory.term * lsymb
  | Generalize   of Theory.term list * naming_pat list option
  | Fa           of fa_arg list
  | TermPat      of int * Theory.term

type parser_args = parser_arg list

let pp_parser_arg ppf = function
  | Int_parsed i  -> Fmt.int ppf (L.unloc i)
  | String_name s -> Fmt.string ppf (L.unloc s)
  | Theory th     -> Theory.pp ppf th
  | NamingPat p   -> pp_naming_pat ppf p
  | IntroPat args -> pp_intro_pats ppf args
  | AndOrPat pat  -> pp_and_or_pat ppf pat
  | SimplPat pat  -> pp_simpl_pat ppf pat

  | RewriteIn (rw_args, in_opt) ->
    Fmt.pf ppf "%a%a"
      (Fmt.list ~sep:Fmt.sp pp_rw_arg) rw_args
      pp_in_target in_opt

  | RewriteEquiv _rw_arg ->
    Fmt.pf ppf "..."

  | Fresh _ 
  | Trans _ ->
    Fmt.pf ppf "..."

  | ApplyIn (_, _, in_opt) ->
    Fmt.pf ppf "... %a" pp_apply_in in_opt

  | HavePt (_, ip, `IntroImpl) ->
    Fmt.pf ppf "... as %a"
      (Fmt.option ~none:Fmt.nop pp_simpl_pat) ip

  | HavePt (_, ip, `None) ->
    Fmt.pf ppf "(%a := ...)"
      (Fmt.option ~none:Fmt.nop pp_simpl_pat) ip

  | ConstSeq (i, _t) -> Fmt.pf ppf "%d: ..." (L.unloc i)

  | SplitSeq (i, _ht, _) -> Fmt.pf ppf "%d ..." (L.unloc i)

  | MemSeq (i, j) -> Fmt.pf ppf "%d %d" (L.unloc i) (L.unloc j)

  | Remember (t, id) ->
    Fmt.pf ppf "%a as %s" Theory.pp t (L.unloc id)

  | Generalize (terms, None) ->
    Fmt.pf ppf "%a" (Fmt.list ~sep:Fmt.sp Theory.pp) terms

  | Generalize (terms, Some _) ->
    Fmt.pf ppf "%a as ..." (Fmt.list ~sep:Fmt.sp Theory.pp) terms

  | TermPat (sel, term) when sel = 1 ->
    Theory.pp ppf term

  | TermPat (sel, term) ->
    Fmt.pf ppf "{%i}(%a)" sel Theory.pp term

  | Fa l ->
    let pp_el ppf (count, term) =
      Fmt.pf ppf "%a%a" pp_rw_count count Theory.pp term
    in
    Fmt.pf ppf "@[<hov> %a@]" (Fmt.list ~sep:Fmt.sp pp_el) l

  | Have _ ->
    Fmt.pf ppf "..."
      
(*------------------------------------------------------------------*)
(** Tactic arguments sorts *)
type _ sort =
  | None      : unit sort

  | Message   : Type.ty sort
  | Boolean   : Type.ty sort
  | Timestamp : Type.ty sort
  | Index     : [`Index] sort

  | Term      : [`Term] sort
  (** Boolean, timestamp or message *)

  | Int       : int L.located sort
  | String    : lsymb sort
  | Pair      : ('a sort * 'b sort) -> ('a * 'b) sort
  | Opt       : 'a sort -> ('a option) sort

(*------------------------------------------------------------------*)

(** Tactic arguments *)
type _ arg =
  | None      : unit arg

  | Message   : Term.term * Type.ty -> Type.ty arg

  | Index     : Vars.var -> [`Index] arg

  | Term      : Type.ty * Term.term * Location.t -> [`Term] arg
  (** A [Term.term] with its sorts. *)

  | Int       : int L.located -> int L.located arg
  | String    : lsymb -> lsymb arg
  | Pair      : 'a arg * 'b arg -> ('a * 'b) arg
  | Opt       : ('a sort * 'a arg option) -> ('a option) arg

(*------------------------------------------------------------------*)

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

(*------------------------------------------------------------------*)
exception Uncastable

let rec cast: type a b. a sort -> b arg -> a arg =
  fun kind t ->
  match kind, t with
  | Pair (a,b), Pair (c,d) -> Pair (cast a c, cast b d)
  | Opt s, Opt (_, None)   -> Opt(s, None)
  | Opt s, Opt (_, Some q) -> Opt(s, Some (cast s q))
  | _ -> begin
      match kind, t with
      | Message  , Message _ -> t
      | Boolean  , Message _ -> t
      | Timestamp, Message _ -> t
      | Index    , Index   _ -> t
      | Term     , Term    _ -> t
      | Int      , Int     _ -> t
      | String   , String  _ -> t
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
  | Term      -> "t"
  | Int       -> "i"
  | String    -> "H"
  | Pair _
  | Opt _ -> assert false

(*------------------------------------------------------------------*)

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
  | Term
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
  | Term
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
  | Term
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
  | Pair (a, b) ->
      Fmt.pf ppf "%a, %a"
        (pp_aux_sort init_table counter_table printopt) a
        (pp_aux_sort init_table counter_table printopt) b

let pp_esort ppf (Sort s) =
  let init_table = setup_counters (empty_table) s in
  let counter_table = ref empty_table in
  pp_aux_sort init_table counter_table false ppf s
