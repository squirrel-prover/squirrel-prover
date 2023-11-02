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

(** find a game in the symbol table *)
val find : Symbols.table -> Theory.lsymb -> game

(*------------------------------------------------------------------*)
val tsubst_var_decl : Type.tsubst -> var_decl -> var_decl 
val tsubst_oracle   : Type.tsubst -> oracle   -> oracle 
val tsubst_game     : Type.tsubst -> game     -> game 

(*------------------------------------------------------------------*)
val pp_var_decl : Format.formatter -> var_decl               -> unit
val pp_sample   : Format.formatter -> Vars.var               -> unit
val pp_update   : Format.formatter -> (Vars.var * Term.term) -> unit
val pp_oracle   : Format.formatter -> oracle                 -> unit
val pp_game     : Format.formatter -> game                   -> unit

(*------------------------------------------------------------------*)
val prove :
    Env.t                   ->
    Hyps.TraceHyps.hyps     ->
    Theory.lsymb            ->
    TacticsArgs.crypto_args ->
    Equiv.equiv             ->
    Term.terms

(*------------------------------------------------------------------*)
(** {2 Front-end types and parsing} *)

module Parse : sig
  type lsymb = Theory.lsymb

  (*------------------------------------------------------------------*)
  (** {3 Types} *)

  (** a randomly sampled variable 
      [name : ty <$] *)
  type var_rnd = {
    vr_name : lsymb ;
    vr_ty   : Theory.p_ty ;
  }

  (** a mutable variable declaration 
      [name : ty = init <$;] *)
  type var_decl = {
    vd_name : lsymb ;
    vd_ty   : Theory.p_ty option ;
    vd_init : Theory.term;
  }

  (** an oracle body *)
  type oracle_body = {
    bdy_rnds    : var_rnd list ;               (** local random samplings *)
    bdy_lvars   : var_decl list ;              (** local variables *)
    bdy_updates : (lsymb * Theory.term) list ; (** state updates *)
    bdy_ret     : Theory.term option ;         (** returned value *)
  }

  (** an oracle declaration *)
  type oracle_decl = {
    o_name  : lsymb ;
    o_args  : Theory.bnds ;
    o_tyout : Theory.p_ty option ;
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
