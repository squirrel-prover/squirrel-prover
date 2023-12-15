module SE = SystemExpr
module Args = TacticsArgs

module THyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
type red_param = { 
  rewrite : bool;         (** user-defined rewriting rules *)
  delta   : Match.delta;  (** replace defined variables by their body *)
  beta    : bool;         (** β-reduction *)
  proj    : bool;         (** reduce projections *)
  zeta    : bool;         (** let reduction *)
  diff    : bool;         (** diff terms reduction *)
  constr  : bool;         (** reduce tautologies over timestamps *)
}

val rp_empty   : red_param
val rp_default : red_param
val rp_full    : red_param
val rp_crypto  : red_param      (** used in cryptographic tactics *)

val parse_simpl_args : red_param -> Args.named_args -> red_param 

(*------------------------------------------------------------------*)

(** Conversion state *)
type cstate

(** Built a convertion state *)
val mk_cstate :
  ?system:SE.context -> 
  ?expand_context:Macros.expand_context -> 
  ?hyps:THyps.hyps ->
  ?param:red_param -> 
  Symbols.table -> 
  cstate

(** Conversion functions using a [cstate] *)
val conv   : cstate -> Term.term  -> Term.term  -> bool 
val conv_g : cstate -> Equiv.form -> Equiv.form -> bool 

(*------------------------------------------------------------------*)
(** {2 Reduction functions} *)

(** Reduction state *)
type state

(*------------------------------------------------------------------*)
(** Make a reduction state directly *)
val mk_state :
  ?expand_context:Macros.expand_context ->
  ?hyps:THyps.hyps ->
  se:SE.arbitrary -> 
  vars:Vars.env -> 
  param:red_param -> 
  Symbols.table -> 
  state

(*------------------------------------------------------------------*)
(** Fully reduces a term *)
val reduce_term : state -> Term.term -> Term.term 

(** Try to reduce once at head position (bool <=> reduction occured) *)
val reduce_head1_term : state -> Term.term -> Term.term * bool

(** Reduces once at head position *)
val whnf_term : state -> Term.term -> Term.term

(*------------------------------------------------------------------*)
(** {2 Reduction functions from a sequent} *)

(*------------------------------------------------------------------*)
module type S = sig
  type t                        (** sequent type *)

  (*------------------------------------------------------------------*)
  (** Build a conversion state from a sequent.  
      [se] is the system of the term being reduced. *)
  val to_state :
    ?expand_context:Macros.expand_context  ->
    ?se:SE.t ->
    ?vars:Vars.env ->
    red_param -> t -> state

  (*------------------------------------------------------------------*)
  val reduce_global :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context ->
    red_param -> t -> Equiv.form -> Equiv.form

  val reduce :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context ->
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  (** Reduces once at head position *)
  val reduce_head1 :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context ->
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a * bool

  (*------------------------------------------------------------------*)
  (** {2 Expantion and destruction modulo } *)

  val destr_eq :
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not :
    t -> 'a Equiv.f_kind -> 'a -> Term.term option

  val destr_or :
    t -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  val destr_and :
    t -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 Conversion from a sequent } *)

  val conv_term :
    ?expand_context:Macros.expand_context ->
    ?se:SE.t ->
    ?param:red_param ->
    t ->
    Term.term -> Term.term -> bool

  val conv_global :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context ->
    ?param:red_param ->
    t ->
    Equiv.form -> Equiv.form -> bool

  val conv_kind :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context ->
    ?param:red_param ->
    t -> 'a Equiv.f_kind ->
    'a -> 'a -> bool

end

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : S with type t := S.t
