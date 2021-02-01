(** Arguments types for tactics, used to unify the declaration of tactics
   requiring type conversions. *)

(*------------------------------------------------------------------*)
(** {2 Intro patterns} *)

type intro_pattern =
  | IP_Star    of Location.t    (** '*' *)
  | IP_Unnamed of Location.t    (** '_' *)
  | IP_AnyName of Location.t    (** '?' *)
  | IP_Named   of Theory.lsymb

  | IP_Or      of intro_pattern list
  (** e.g. \[H1 | H2\] to do a case on a disjunction. *)
        
  | IP_And     of intro_pattern list
  (** e.g. \[H1 H2\] to destruct a conjunction. *)

  | IP_Split 
  (** e.g. \[\] to split a disjunction or conjunction. *)

val pp_intro_args : Format.formatter -> intro_pattern list -> unit
  
(*------------------------------------------------------------------*)
(** {2 Tactic arguments types} *)
  
(** Types used during parsing. 
    Note that all tactics not defined in the parser must rely on the Theory 
    type, even to parse strings. *)
type parser_arg =
  | String_name of string
  | Int_parsed  of int
  | Theory      of Theory.term
  | IntroPat    of intro_pattern list

(** Tactic arguments sorts *)
type _ sort =
  | None      : unit sort

  | Message   : Sorts.message   sort
  | Boolean   : Sorts.boolean   sort
  | Timestamp : Sorts.timestamp sort        
  | Index     : Sorts.index     sort
        
  | ETerm     : Theory.eterm    sort
  (** Boolean, timestamp or message *)

  | Int       : int sort
  | String    : string sort
  | Pair      : ('a sort * 'b sort) -> ('a * 'b) sort
  | Opt       : 'a sort -> ('a option) sort

(** Tactic arguments *)
type _ arg =
  | None      : unit arg 

  | Message   : Term.message   -> Sorts.message   arg
  | Boolean   : Term.formula   -> Sorts.boolean   arg
  | Timestamp : Term.timestamp -> Sorts.timestamp arg
  | Index     : Vars.index     -> Sorts.index     arg

  | ETerm     : 'a Sorts.sort * 'a Term.term * Location.t -> Theory.eterm arg
  (** A [Term.term] with its sorts. *)
        
  | Int       : int -> int arg
  | String    : string -> string arg
  | Pair      : 'a arg * 'b arg -> ('a * 'b) arg
  | Opt       : ('a sort * 'a arg option) -> ('a option) arg

(*------------------------------------------------------------------*)
val sort : 'a arg -> 'a sort

type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

(*------------------------------------------------------------------*)
exception Uncastable

val cast:  'a sort -> 'b arg -> 'a arg

(*------------------------------------------------------------------*)
val pp_esort : Format.formatter -> esort -> unit

(*------------------------------------------------------------------*)
(** {2 Argument conversion} *)

val convert_as_string : parser_arg list -> string option
  
val convert_args :
  Symbols.table -> Vars.env ->
  parser_arg list -> esort -> earg


(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type tac_arg_error_i =
  | CannotConvETerm 

type tac_arg_error = Location.t * tac_arg_error_i

exception TacArgError of tac_arg_error

val pp_tac_arg_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> tac_arg_error -> unit

