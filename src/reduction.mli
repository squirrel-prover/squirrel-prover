module SE = SystemExpr
module Args = TacticsArgs

module THyps = Hyps.TraceHyps
  
(*------------------------------------------------------------------*)
type red_param = { 
  delta  : bool;
  beta   : bool;
  constr : bool;
}

val rp_default : red_param
val rp_full    : red_param

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
val conv_e : cstate -> Equiv.form -> Equiv.form -> bool 

(*------------------------------------------------------------------*)
module type S = sig
  type t                        (* type of sequent *)

  (*------------------------------------------------------------------*)
  (** {2 reduction } *)
    
  val reduce_term  :
    ?expand_context:Macros.expand_context -> 
    ?se:SE.t -> 
    red_param -> t -> Term.term -> Term.term     

  val reduce_equiv : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    red_param -> t -> Equiv.form -> Equiv.form

  val reduce : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  (*------------------------------------------------------------------*)
  (** {2 expantion and destruction modulo } *)
    
  val expand_head_once :
    ?expand_context:Macros.expand_context ->
    ?se:SE.t -> 
    red_param -> t -> Term.term -> Term.term * bool

  val destr_eq : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not : 
    t -> 'a Equiv.f_kind -> 'a -> Term.term option

  val destr_and : 
    t -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 conversion from a sequent } *)

  val conv_term :
    ?expand_context:Macros.expand_context -> 
    ?se:SE.t -> 
    ?param:red_param ->
    t ->
    Term.term -> Term.term -> bool

  val conv_equiv : 
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
