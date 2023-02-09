(** Arguments types for tactics, used to unify the declaration of tactics
   requiring type conversions. *)

module L = Location

module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** Tactic target. *)
type in_target = [`Goal | `All | `Hyps of lsymb list]


(*------------------------------------------------------------------*)
(** {2 Tactics named arguments} *)

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

(** Rewrite argument, which is a rewrite or simplification item *)
type rw_arg =
  | R_item   of rw_item
  | R_s_item of s_item

(*------------------------------------------------------------------*)
(** Function application argument *)
type fa_arg = rw_count * Theory.term
                           
(*------------------------------------------------------------------*)
type apply_in = lsymb option

(*------------------------------------------------------------------*)
(** {2 Intro patterns} *)

type naming_pat =
  | Unnamed   (** '_' *)
  | AnyName   (** '?' *)
  | Named of string
  | Approx  of string        (** only used internally *)

type and_or_pat =
  | Or      of simpl_pat list
  (** e.g. \[H1 | H2\] to do a case on a disjunction. *)

  | Split
  (** \[\] to do a case. *)

  | And     of simpl_pat list
  (** e.g. \[H1 H2\] to destruct a conjunction. *)

and simpl_pat =
  | SAndOr of and_or_pat
  | SNamed of naming_pat
  | Srewrite of rw_dir                    (** -> or <-*)

type intro_pattern =
  | Star   of Location.t    (** [*] *)
  | StarV  of Location.t    (** [>] *)
  | SItem  of s_item
  | SExpnd of expnd_item    (** [@/macro] *)
  | Simpl  of simpl_pat

(*------------------------------------------------------------------*)
val pp_naming_pat : Format.formatter -> naming_pat         -> unit
val pp_and_or_pat : Format.formatter -> and_or_pat         -> unit
val pp_simpl_pat  : Format.formatter -> simpl_pat          -> unit
val pp_intro_pat  : Format.formatter -> intro_pattern      -> unit
val pp_intro_pats : Format.formatter -> intro_pattern list -> unit


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
(** {2 Tactic arguments types} *)


(** Types used during parsing.
    Note that all tactics not defined in the parser must rely on the Theory
    type, even to parse strings. *)
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
val pp_parser_arg : Format.formatter -> parser_arg -> unit

(*------------------------------------------------------------------*)
type esort = Sort : ('a sort) -> esort

type earg = Arg : ('a arg) -> earg

(*------------------------------------------------------------------*)
exception Uncastable

val cast:  'a sort -> 'b arg -> 'a arg

(*------------------------------------------------------------------*)
val pp_esort : Format.formatter -> esort -> unit

