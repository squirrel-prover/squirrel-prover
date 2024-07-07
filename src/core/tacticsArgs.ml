(** Abstract syntax for tactic arguments,
    and mechanisms for parsing typed arguments. *)

module L = Location

module SE = SystemExpr

type lsymb = Symbols.lsymb

(** {2 Tactics args}

    Abstract syntax for tactic arguments. *)

(*------------------------------------------------------------------*)
(** Tactic target. *)
type in_target = [
  | `Goal
  | `All
  | `HypsOrDefs of lsymb list
    (** Hypotheses, definitions, or frame elements. *)
]

(*------------------------------------------------------------------*)
(** {3 Named arguments}
    These are often used with [lsymb] parameters,
    but sometimes with arbitrary [parser_arg] parameters,
    which allows e.g. passing integers as named arguments. *)

type 'a named_arg =
  | NArg  of lsymb            (** [~id] *)
  | NList of lsymb * 'a list  (** [~id:[id1, ..., idn]] *)

type named_args = lsymb named_arg list

(*------------------------------------------------------------------*)
(** {3 Simplification item} *)
    
type s_item_body =
  | Tryauto      of Location.t    (** [//] *)
  | Tryautosimpl of Location.t    (** [//] *)
  | Simplify     of Location.t    (** [//=] *)

type s_item = s_item_body * named_args

let s_item_loc (s,_) = match s with Tryauto l | Tryautosimpl l | Simplify l -> l

(*------------------------------------------------------------------*)
(** {3 Parsed arguments for rewrite} *)

type rw_count = 
    | Once                   (** [ε] *)
    | Many                   (** [!] *)
    | Any                    (** [?] *)
    | Exact of int           (** [i!] where [i] is an integer *)

type rw_dir = [`LeftToRight | `RightToLeft ] L.located

(** General rewrite item *)
type 'a rw_item_g = {
  rw_mult : rw_count;
  rw_dir  : rw_dir;
  rw_type : 'a;
}

(** Rewrite or expand item *)
type rw_item = [
  | `Rw        of Theory.pt
  | `Expand    of Symbols.p_path
  | `ExpandAll of Location.t
] rw_item_g

(** Expand item *)
type expnd_item = [
  | `Expand    of Symbols.p_path
  | `ExpandAll of Location.t
] rw_item_g

(** Rewrite equiv item *)
type rw_equiv_item = [
  | `Rw of Theory.pt
] rw_item_g

(** Rewrite argument, which is a rewrite or simplification item. *)
type rw_arg =
  | R_item   of rw_item
  | R_s_item of s_item

(*------------------------------------------------------------------*)
(** Function application argument *)
type fa_arg = rw_count * Theory.term

(*------------------------------------------------------------------*)
type apply_in = lsymb option

(*------------------------------------------------------------------*)
(** {3 Intro patterns} *)

type naming_pat =
  | Unnamed                  (** [_] *)
  | AnyName                  (** [?] *)
  | Named   of string
  | Approx  of string        (** only used internally *)

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
  | Srewrite of rw_dir      (** [->] or [<-] *)

type intro_pattern =
  | SClear of lsymb list    (** [{H H' ...}] *)
  | Star   of Location.t    (** [*] *)
  | StarV  of Location.t    (** [>] *)
  | SItem  of s_item
  | SExpnd of expnd_item    (** [@/macro] *)
  | Simpl  of simpl_pat

(*------------------------------------------------------------------*)
(** {3 Fresh tactic arguments} *)

type fresh_arg =
  | FreshInt of int L.located
  | FreshHyp of lsymb

(*------------------------------------------------------------------*)
(** {3 Trans tactic arguments} *)

type trans_arg =
  | TransSystem of SE.Parse.sys
  | TransTerms  of (int L.located * Theory.term) list

(*------------------------------------------------------------------*)
(** {3 Have tactic arguments} *)

(** before, simpl pat for produced hypothesis, after *)
type have_ip = s_item list * simpl_pat * s_item list

type have_arg    = have_ip option * Theory.any_term
type have_pt_arg = Theory.pt * have_ip option * [`IntroImpl | `None]

(*------------------------------------------------------------------*)
(** {3 Diffie-Hellman tactics arguments} *)

type dh_arg =
  | CDH of { hyp : Symbols.lsymb; gen : Symbols.p_path; }
  | GDH of { hyp : Symbols.lsymb; gen : Symbols.p_path; }
  | DDH of { gen : Symbols.p_path;
             na  : Symbols.p_path;
             nb  : Symbols.p_path;
             nc  : Symbols.p_path; }

(*------------------------------------------------------------------*)
(** {3 Crypto tactic arguments} *)

(** [{glob_sample = k; term; bnds; cond }] add the constraints that
    [k] must be mapped to [term] for any [bnds] such that [cond]. *)
type crypto_arg = { 
  glob_sample : lsymb; 
  term        : Theory.term;
  bnds        : Theory.bnds option;
  cond        : Theory.term option;
}

type crypto_args = crypto_arg list

(*------------------------------------------------------------------*)
(** {3 General AST for tactic arguments} *)

(** Tactics not having a specific treatment in the parser can only
    receive a small subset of [parser_arg]s, defined through
    [Parser.tactic_params]. *)

(** A parsed tactic argument. *)
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
  | ApplyIn      of named_args * Theory.pt * apply_in
  | Have         of have_arg
  | HavePt       of have_pt_arg
  | Named_args   of named_args
      (** Named arguments whose values are just symbols. *)
  | Named_args_gen of parser_arg named_arg list
      (** General named arguments whose values are [parser_arg]s. *)
  | SplitSeq     of int L.located * Theory.term * Theory.term option
  | ConstSeq     of int L.located * (Theory.term * Theory.term) list
  | MemSeq       of int L.located * int L.located
  | Remember     of Theory.term * lsymb
  | Generalize   of Theory.term list * naming_pat list option
  | Fa           of fa_arg list
  | TermPat      of int * Theory.term
  | DH           of dh_arg
  | Crypto       of Symbols.p_path * crypto_args

type parser_args = parser_arg list
      
(*------------------------------------------------------------------*)
(** {2 Typed arguments}

    Typed representation of arguments, to be provided (after parsing)
    to the actual tactic implementations. This is only (?) used for
    tactics registered via [ProverTactics.register_typed]. *)

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
