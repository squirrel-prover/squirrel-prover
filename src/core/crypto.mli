open Ppenv

module SE = SystemExpr
module L = Location

(*------------------------------------------------------------------*)
(** a variable declaration, with an initial value *)
type var_decl = {
  var  : Vars.var ;
  init : Term.term ;
}

(** An stateful oracle in a cryptographic game *)
type oracle = {
  name      : string ;
  args      : Vars.vars ;
  loc_smpls : Vars.vars ;       (** local random samplings *)
  loc_vars  : var_decl list;    (** local (non-mutable) variables *)
  updates   : (Vars.var * Term.term) list ;
  output    : Term.term ;
}

(** A cryptographic game *)
type game = {
  name       : string ;
  glob_smpls : Vars.var list ; (** global random samplings *)
  glob_vars  : var_decl list     ; (** global (mutable) variables *)
  oracles    : oracle list   ;
}

(*------------------------------------------------------------------*)
(** add game objects in the symbol table *)
type Symbols.data += Game of game

val data_as_game : Symbols.data -> game

(** find a game in the symbol table *)
val find : Symbols.table -> Symbols.p_path -> game

(*------------------------------------------------------------------*)
val tsubst_var_decl : Type.tsubst -> var_decl -> var_decl 
val tsubst_oracle   : Type.tsubst -> oracle   -> oracle 
val tsubst_game     : Type.tsubst -> game     -> game 

(*------------------------------------------------------------------*)
val _pp_var_decl : var_decl               formatter_p
val _pp_sample   : Vars.var               formatter_p
val _pp_update   : (Vars.var * Term.term) formatter_p
val _pp_oracle   : oracle                 formatter_p
val _pp_game     : game                   formatter_p

(*------------------------------------------------------------------*)
val prove :
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
      [name : ty <$] *)
  type var_rnd = {
    vr_name : lsymb ;
    vr_ty   : Typing.ty ;
  }

  (** a mutable variable declaration 
      [name : ty = init <$;] *)
  type var_decl = {
    vd_name : lsymb ;
    vd_ty   : Typing.ty option ;
    vd_init : Typing.term;
  }

  (** an oracle body *)
  type oracle_body = {
    bdy_rnds    : var_rnd list ;               (** local random samplings *)
    bdy_lvars   : var_decl list ;              (** local variables *)
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
    g_gvar    : var_decl list ;    (** global (mutable) variables *)
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
