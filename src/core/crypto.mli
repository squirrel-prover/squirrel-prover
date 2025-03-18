open Ppenv

module SE = SystemExpr
module L = Location

(*------------------------------------------------------------------*)
(** a variable declaration, with an initial value *)
type var_decl = {
  var  : Vars.var ;
  init : Term.term ;
}

type var_decls = var_decl list

(** a stateful oracle in a cryptographic game *)
type oracle = {
  name      : string ;
  args      : Vars.vars ;
  loc_smpls : Vars.vars ;       (** local random samplings *)
  loc_vars  : var_decls;        (** local (mutable) variables *)
  updates   : (Vars.var * Term.term) list ;
  output    : Term.term ;
}

(** a global variable declaration *)
type gdecl =
  | Mutable of Term.t           (** mutable variable ands its initial value *)
  | Let     of Term.t           (** non-mutable variable and its value *)
  | LetInit                     (** adversarially-controled non-mutable variable *)

(** a global variable declaration *)
type gvar_decl = Vars.var * gdecl

(** a cryptographic game *)
type game = {
  name       : string ;
  glob_smpls : Vars.var list ;  (** global random samplings *)
  glob_vars  : gvar_decl list ; (** global variables (mutable or let) *)
  oracles    : oracle list   ;
}

(*------------------------------------------------------------------*)
(** add game objects in the symbol table *)
type Symbols.data += Game of game

val data_as_game : Symbols.data -> game

(** find a game in the symbol table *)
val find : Symbols.table -> Symbols.p_path -> game

(*------------------------------------------------------------------*)
val gsubst_oracle : oracle   Subst.substitution
val gsubst_game   : game     Subst.substitution

(*------------------------------------------------------------------*)
val _pp_oracle   : oracle formatter_p
val _pp_game     : game   formatter_p

(*------------------------------------------------------------------*)
type param = { 
  subgoal_on_failure : bool; 
  (** When [crypto] cannot deduce a term [(t | ϕ)], does it abandon
      the proof and fail ([subgoal_on_failure=true]) or generate a
      proof-obligation. *)
}

(** default options *)
val param : param

(*------------------------------------------------------------------*)
val prove :
  param:param             ->
  Env.t                   ->
  Hyps.TraceHyps.hyps     ->
  Symbols.p_path          ->
  TacticsArgs.crypto_args ->
  Equiv.equiv             ->
  Term.terms

(*------------------------------------------------------------------*)
(** {2 Front-end types and parsing} *)

module Parse : sig
  type lsymb = Symbols.lsymb

  (*------------------------------------------------------------------*)
  (** {3 Types} *)

  (** a randomly sampled variable 
      [rnd name : ty] *)
  type var_rnd = {
    vr_name : lsymb ;
    vr_ty   : Typing.ty ;
  }

  (** a global variable declaration 
      - [var name : ty = init;]
      - [let name : ty = init;] 
      - [let name : ty = #init;] (here, the string "#init" must appear
        verbatim) *)
  type gvar_decl = {
    gvd_name    : lsymb ;
    gvd_ty      : Typing.ty option ;
    gvd_content : [`Mutable of Typing.term | `Let of Typing.term | `LetInit ];
  }

  (** an oracle body *)
  type oracle_body = {
    bdy_rnds    : var_rnd list ;               (** local random samplings *)
    bdy_lvars   : gvar_decl list ;             (** local variables (only mutable allowed) *)
    bdy_updates : (lsymb * Typing.term) list ; (** state updates *)
    bdy_ret     : Typing.term option ;         (** returned value *)
  }

  (** an oracle declaration *)
  type oracle_decl = {
    o_name  : lsymb ;
    o_args  : Typing.bnds ;
    o_tyout : Typing.ty option ;
    o_body  : oracle_body ;
  }

  (** a game declaration *)
  type game_decl = {
    g_name    : lsymb ; 
    g_rnds    : var_rnd list ;     (** global (initial) samplings *)
    g_gvar    : gvar_decl list ;   (** global (mutable or let) variables *)
    g_oracles : oracle_decl list ; (** the oracles *)
  }

  (*------------------------------------------------------------------*)
  (** {3 Error handling} *)

  type error_i = Failure of string

  type error = L.t * error_i

  exception Error of error

  val pp_error : 
    (Format.formatter -> Location.t -> unit) ->
    Format.formatter -> error -> unit
  
  (*------------------------------------------------------------------*)
  (** {3 Parsing} *)

  val parse : L.t -> Symbols.table -> game_decl -> game
end
