module SE = SystemExpr
module Args = TacticsArgs

module THyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** {2 Core reduction functions} 

    Allow to avoid the cyclic dependency between [Reduction] and
    [Match] (see [ReductionCore] for details). *)

include ReductionCore.S

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
    ?system:SE.context ->
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
    t -> mode:SmartFO.mode -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 Conversion from a sequent } *)

  val conv_term :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context ->
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
