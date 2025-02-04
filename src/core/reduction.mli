(*------------------------------------------------------------------*)
(** {2 Core reduction functions} 

    Allow to avoid the cyclic dependency between [Reduction] and
    [Match] (see [ReductionCore] for details). *)

(** Reduction is exact without any probabilistic approximation but for
    the happens hypotheses used. *)

include module type of ReductionCore

include ReductionCore.Sig

(*------------------------------------------------------------------*)
(** {2 Reduction functions from a sequent} *)

(*------------------------------------------------------------------*)
module type S = sig
  type t                        (** sequent type *)

  (*------------------------------------------------------------------*)
  (** Build a reduction state from a sequent.  
      The term to be reduced is taken in [system.set]. *)
  val to_state :
    ?system:SE.context ->
    ?vars:Vars.env ->
    red_param -> ?concrete:bool -> t -> state

  (*------------------------------------------------------------------*)
  val reduce_global :
    ?system:SE.context ->
    red_param -> t -> 
    Equiv.form -> Equiv.form
  
  val reduce :
    ?system:SE.context ->
    red_param -> ?concrete:bool -> t -> 
    'a Equiv.f_kind -> 'a -> 'a
  
  (** Reduces once at head position *)
  val reduce_head1 :
    ?system:SE.context ->
    red_param -> ?concrete:bool -> t -> 
    'a Equiv.f_kind -> 'a -> 'a * head_has_red
  
  (*------------------------------------------------------------------*)
  (** {2 Expantion and destruction modulo } *)

  val destr_eq :
    ?concrete:bool -> t -> 
    'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not :
    ?concrete:bool -> t ->
    'a Equiv.f_kind -> 'a -> Term.term option

  val destr_or :
    ?concrete:bool -> t ->
    'a Equiv.f_kind -> 'a -> ('a * 'a) option

  val destr_and :
    ?concrete:bool -> t ->
    mode:SmartFO.mode -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 Conversion from a sequent } *)

  val conv_term :
    ?system:SE.context ->
    ?param:red_param -> ?concrete:bool ->
    t ->
    Term.term -> Term.term -> bool

  val conv_global :
    ?system:SE.context ->
    ?param:red_param -> 
    t ->
    Equiv.form -> Equiv.form -> bool

  val conv_kind :
    ?system:SE.context ->
    ?param:red_param -> ?concrete:bool -> 
    t -> 'a Equiv.f_kind ->
    'a -> 'a -> bool

end

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : S with type t := S.t
